import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafD
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntrySupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.FrozenCoherence

/-!
# The displayed requests of the tail never decrease

Monotonicity of the tail's output in the outer time, `grayTail_output_monotone`. The step
analysis distinguishes the three shapes a tail step can take — a terminated state only advances
its clock, a round meeting the robust gray goal is frozen and its surviving children become the
new slots, and a round missing the goal only appends
(`grayTailStep_eq_of_done_or_slots_empty`, `grayTailStep_eq_of_goal_true`,
`grayTailStep_eq_of_goal_false`) — and the monotonicity of the assembled quantities in their
inputs (`grayTailSonBase_slotEntries_mono`, `grayTailEntryMove_mono_move`). Also here are the
floor estimate `grayTailTargetFloor_avoidsSmall` and the elementary summation lemma
`sum_ge_of_forall_zero_or_ge`.
-/



namespace Kolmogorov
open scoped BigOperators

/-- The son base is monotone in the root requests of the slot moves. -/
lemma grayTailSonBase_slotEntries_mono {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (move1 move2 : FamilyClientMove)
    (hmove : ∀ j < slots.length,
      getReq (familyClientMoveAt move1 j) [] ≤ getReq (familyClientMoveAt move2 j) [])
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move1) i c ≤
      grayTailSonBase (grayTailSlotEntries slots move2) i c := by
  rw [grayTailSonBase_slotEntries_eq_sum, grayTailSonBase_slotEntries_eq_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact hmove j.val j.isLt
  · exact le_rfl

/-- The slot entries of a cons list pair the first slot with the first move and recurse. -/
lemma grayTailSlotEntries_cons {n b : ℕ} (s : GrayTailSlot n b)
    (rest : List (GrayTailSlot n b)) (move : FamilyClientMove) :
    grayTailSlotEntries (s :: rest) move =
      (s, familyClientMoveAt move 0) :: grayTailSlotEntries rest (List.tail move) := by
  unfold grayTailSlotEntries familyClientMoveAt
  rw [List.ofFn_succ]
  congr 1
  ext j
  cases move <;> simp

/-- The move assembled for a slot is monotone in the moves of the slots it is built from. -/
lemma grayTailEntryMove_mono_move {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (move1 move2 : FamilyClientMove)
    (hmove : ∀ j < slots.length, ∀ y,
      getReq (familyClientMoveAt move1 j) y ≤ getReq (familyClientMoveAt move2 j) y)
    (slot : GrayTailSlot n b) (y : GacsDayNode) :
    getReq (grayTailEntryMove (grayTailSlotEntries slots move1) slot) y ≤
      getReq (grayTailEntryMove (grayTailSlotEntries slots move2) slot) y := by
  induction slots generalizing move1 move2 with
  | nil =>
      unfold grayTailEntryMove grayTailSlotEntries
      simp
  | cons s rest ih =>
      rw [grayTailSlotEntries_cons s rest move1, grayTailSlotEntries_cons s rest move2]
      unfold grayTailEntryMove
      simp only [List.find?_cons]
      by_cases hs : s = slot
      · simp only [hs, decide_true, Option.map_some, Option.getD_some]
        exact hmove 0 (by simp) y
      · simp only [hs, decide_false]
        apply ih move1.tail move2.tail
        intro j hj y'
        have hj' : j + 1 < (s :: rest).length := by simp [hj]
        have hmove_j := hmove (j + 1) hj' y'
        cases move1 <;> cases move2 <;> exact hmove_j

/-- A terminated tail state only advances its clock. -/
lemma grayTailStep_eq_of_done_or_slots_empty
    {n b q L a e : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hdone : (st.done || st.slots.isEmpty) = true) :
    grayTailStep q L a e sigma A st sm = { st with time := st.time + 1 } := by
  rw [grayTailStep_eq]
  simp [hdone]

/-- A round that meets the robust gray goal is frozen, the surviving children become the new
slots and the tail finishes if few slots survive or the round budget is spent. -/
lemma grayTailStep_eq_of_goal_true {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayTailState n b} {sm : FamilyServerMove}
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true) :
    grayTailStep q L a e sigma A st sm =
      let r := st.frozen.length
      let epsRound := grayTailRoundEps q L e r
      let deltaRound := grayTailRoundDelta q L e r
      let current := grayTailCurrentMove q L e sigma st
      let localSM := grayTailLocalServerMove deltaRound st.slots sm
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.frozen ++
        [{ serverTime := st.time, roundIndex := r, epsDepth := epsRound,
           slots := st.slots, move := current, allocated := allocated,
           unavailable := st.unavailable }]
      let unavailable' := st.unavailable ++ neighborhoodCellsList epsRound allocated
      let threshold := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
      let candidates := grayTailNextSlots e (2 ^ (e - a))
        frozen'.length threshold A frozen' sm
      let stop := grayTailGlobalQuarterB (n := n) (2 ^ (e - a)) candidates
      let done' := stop || decide (grayTailRoundCount q ≤ frozen'.length)
      { time := st.time + 1, roundStart := st.time + 1, done := done',
        frozen := frozen', unavailable := unavailable', slots := candidates,
        anchoringSlots := [], history := ([], []) } := by
  rw [grayTailStep_eq]
  simp [hdone_empty, hgoal]

/-- A round that misses the goal only appends the current move and the localised server move to
the history. -/
lemma grayTailStep_eq_of_goal_false {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayTailState n b} {sm : FamilyServerMove}
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = false) :
    grayTailStep q L a e sigma A st sm =
      let deltaRound := grayTailRoundDelta q L e st.frozen.length
      let current := grayTailCurrentMove q L e sigma st
      let localSM := grayTailLocalServerMove deltaRound st.slots sm
      { st with
        time := st.time + 1
        history := (st.history.1 ++ [current], st.history.2 ++ [localSM]) } := by
  rw [grayTailStep_eq]
  simp [hdone_empty, hgoal]

/-- A terminated tail state displays the same output after a step. -/
lemma grayTailOutput_step_eq_of_done_or_slots_empty
    {n b q L a e : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hdone : (st.done || st.slots.isEmpty) = true) :
    grayTailOutput q L a e sigma (grayTailStep q L a e sigma A st sm) =
      grayTailOutput q L a e sigma st := by
  rw [grayTailStep_eq_of_done_or_slots_empty st sm hdone]
  rfl

/-- Freezing one more round appends that round's slot entries to the frozen entries. -/
lemma grayTailFrozenEntries_append_one {n b : ℕ}
    (frozen : GrayTailFrozen n b) (p : GrayTailRound n b) :
    grayTailFrozenEntries (frozen ++ [p]) =
      grayTailFrozenEntries frozen ++ grayTailSlotEntries p.slots p.move := by
  unfold grayTailFrozenEntries
  simp only [List.flatMap_append, List.flatMap_singleton]

/-- The entries after freezing a round are the old frozen entries, that round's entries, and the
new slots with the new move. -/
lemma grayTailEntries_append_round {n b : ℕ}
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (move : FamilyClientMove) (slots' : List (GrayTailSlot n b)) (move' : FamilyClientMove)
    (t r eps : ℕ) (alloc : List BitString) (unav : Allocation) :
    grayTailEntries (frozen ++ [{ serverTime := t, roundIndex := r, epsDepth := eps, slots := slots,
                                  move := move, allocated := alloc, unavailable :=
      unav }]) slots' move' =
      grayTailEntries frozen slots move ++ grayTailSlotEntries slots' move' := by
  unfold grayTailEntries
  rw [grayTailFrozenEntries_append_one]

/-- With the frozen rounds fixed, the move assembled for a slot is monotone in the current move. -/
lemma grayTailEntryMove_mono_append_of_frozen {n b : ℕ}
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (move1 move2 : FamilyClientMove)
    (hmove : ∀ j < slots.length, ∀ y,
      getReq (familyClientMoveAt move1 j) y ≤ getReq (familyClientMoveAt move2 j) y)
    (slot : GrayTailSlot n b) (y : GacsDayNode) :
    getReq (grayTailEntryMove (grayTailEntries frozen slots move1) slot) y ≤
      getReq (grayTailEntryMove (grayTailEntries frozen slots move2) slot) y := by
  unfold grayTailEntries grayTailEntryMove
  rw [List.find?_append, List.find?_append]
  cases hfind : (grayTailFrozenEntries frozen).find? (fun p => decide (p.1 = slot)) with
  | some pr => simp
  | none =>
      simp only [Option.none_or]
      exact grayTailEntryMove_mono_move slots move1 move2 hmove slot y

/-- A son base built from nonnegative slot requests is nonnegative. -/
lemma grayTailSonBase_slotEntries_nonneg {n b : ℕ}
    (slots : List (GrayTailSlot n b)) (cm : FamilyClientMove)
    (hcm : ∀ j < slots.length, 0 ≤ getReq (familyClientMoveAt cm j) [])
    (i : Fin n) (c : Fin b) :
    0 ≤ grayTailSonBase (grayTailSlotEntries slots cm) i c := by
  rw [grayTailSonBase_slotEntries_eq_sum]
  exact Finset.sum_nonneg fun j _ => by
    split_ifs with h
    · exact hcm j.val j.isLt
    · exact le_rfl

/-- Every slot entry of a nonnegative family move requests a nonnegative amount at every node. -/
lemma getReq_slotEntries_mem_nonneg {n b : ℕ} (slots : List (GrayTailSlot n b)) (cm :
                                                                                  FamilyClientMove)
    (hcm : ∀ j < slots.length, ∀ y, 0 ≤ getReq (familyClientMoveAt cm j) y)
    (pr : GrayTailSlot n b × ClientMove) (hpr : pr
                                           ∈ grayTailSlotEntries slots cm) (y : GacsDayNode) :
    0 ≤ getReq pr.2 y := by
  unfold grayTailSlotEntries at hpr
  rw [List.mem_ofFn] at hpr
  obtain ⟨j, rfl⟩ := hpr
  exact hcm j.val j.isLt y

/-- Along a certified history against a legal play, the current move of the tail requests a
nonnegative amount at every node. -/
lemma getReq_currentMove_nonneg {n q L B a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayTailState n (grayTailBranch q L a e)}
    (ha : 1 ≤ a) (hae : a ≤ e) (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) (hcert : GrayTailCertified q L e A sm t st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hround : st.done = false → st.frozen.length < grayTailRoundCount q)
    (j : ℕ) (hj : j < st.slots.length) (y : GacsDayNode) :
    0
      ≤ getReq (familyClientMoveAt (if st.done then [] else grayTailCurrentMove q L e sigma
                                     st) j) y := by
  by_cases hd : st.done
  · simp [hd, familyClientMoveAt, getReq]
  · have hcur : (if st.done then [] else grayTailCurrentMove q L e sigma st)
      = grayTailCurrentMove q L e sigma st := by simp [hd]
    rw [hcur]
    have hd_false : st.done = false := Bool.eq_false_of_not_eq_true hd
    by_cases hempty : st.slots.isEmpty
    · have hlen : st.slots.length = 0 := List.isEmpty_iff_length_eq_zero.mp hempty
      omega
    · have hd_ne : (st.done || st.slots.isEmpty) ≠ true := by
        cases h1 : st.done <;> cases h2 : st.slots.isEmpty <;> simp [h1, h2] at hd hempty ⊢
      have hb : grayTailBaseBranch q L ≤ grayTailBranch q L a e := le_max_right _ _
      have hspec := grayTailRound_gameSpec ha hae hB hRung hcert hd_ne hb
      have hfs_legal := grayTailFutureServer_legal hcert (hround hd_false) hsm
      have hlegal := hspec.weak.legal (grayTailFutureServer q L e st sm) hfs_legal
      have hcurr := grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace
      rw [hcurr]
      exact (hlegal.1 st.history.2.length j hj).1 y

/-- Freezing a round appends the entries of the new slots to the displayed entries. -/
lemma grayTailOutputEntries_step_of_goal_true {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayTailState n b} {sm : FamilyServerMove}
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true) :
    grayTailOutputEntries q L e sigma (grayTailStep q L a e sigma A st sm) =
      grayTailOutputEntries q L e sigma st ++
        grayTailSlotEntries (grayTailStep q L a e sigma A st sm).slots
          (if (grayTailStep q L a e sigma A st sm).done then [] else grayTailCurrentMove q L e sigma
            (grayTailStep q L a e sigma A st sm)) := by
  have hnot_done : st.done = false := by
    cases hd : st.done <;> [rfl; simp [hd] at hdone_empty]
  have hstep := grayTailStep_eq_of_goal_true (a := a) (A := A) hdone_empty hgoal
  unfold grayTailOutputEntries grayTailEntries
  rw [hstep]
  dsimp only
  rw [grayTailFrozenEntries_append_one, List.append_assoc]
  simp [hnot_done]

/-- A step that misses the goal keeps the frozen rounds and slots, and only replaces the current
move. -/
lemma grayTailOutputEntries_step_of_goal_false {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayTailState n b} {sm : FamilyServerMove}
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = false) :
    grayTailOutputEntries q L e sigma (grayTailStep q L a e sigma A st sm) =
      grayTailEntries st.frozen st.slots (grayTailCurrentMove q L e sigma (grayTailStep q L a e
                                                                            sigma A st sm)) := by
  have hnot_done : st.done = false := by
    cases hd : st.done <;> [rfl; simp [hd] at hdone_empty]
  have hstep := grayTailStep_eq_of_goal_false (a := a) (A := A) hdone_empty hgoal
  unfold grayTailOutputEntries grayTailEntries
  rw [hstep]
  dsimp only
  simp [hnot_done]

/-- From a terminated state, a step does not decrease the displayed request at any node. -/
lemma grayTailOutput_step_mono_of_done_or_slots_empty
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (sm : ℕ → FamilyServerMove) (t : ℕ)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hdone_empty : (st.done || st.slots.isEmpty) = true)
    (i : ℕ) (_hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayTailOutput q L a e sigma st) i x ≤
      getFamilyReq
        (grayTailOutput q L a e sigma (grayTailStep q L a e sigma A st (sm t))) i x := by
  rw [grayTailOutput_step_eq_of_done_or_slots_empty st (sm t) hdone_empty]

/-- The tail output is monotone in its entries: growing every son base and every entry move grows
the displayed request. -/
lemma getFamilyReq_grayTailOutput_mono
    (a : ℕ) {n b q L e i : ℕ} {sigma : FamilyStrategyScheme}
    {st1 st2 : GrayTailState n b} (hi : i < n) (x : GacsDayNode)
    (hdone : st1.done = true → st2.done = true)
    (hbase : ∀ c : Fin b,
      grayTailSonBase (grayTailOutputEntries q L e sigma st1) ⟨i, hi⟩ c ≤
        grayTailSonBase (grayTailOutputEntries q L e sigma st2) ⟨i, hi⟩ c)
    (hentry : ∀ (slot : GrayTailSlot n b) (y : GacsDayNode),
      getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st1) slot) y ≤
        getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st2) slot) y) :
    getFamilyReq (grayTailOutput q L a e sigma st1) i x ≤
      getFamilyReq (grayTailOutput q L a e sigma st2) i x := by
  change getReq (familyClientMoveAt (grayTailOutput q L a e sigma st1) i) x ≤
    getReq (familyClientMoveAt (grayTailOutput q L a e sigma st2) i) x
  rw [familyClientMoveAt_grayTailOutput st1 hi, familyClientMoveAt_grayTailOutput st2 hi]
  rcases x with _ | ⟨c, _ | ⟨c', y⟩⟩
  · rw [getReq_graftTwoLevel_root, getReq_graftTwoLevel_root]
    exact grayTailRootRequest_mono ⟨i, hi⟩ hdone
      (fun c => grayTailSonRequest_mono (grayTailThreshold_le_eps q e) ⟨i, hi⟩ c (hbase c))
  · by_cases hc : c < b
    · rw [getReq_graftTwoLevel_son hc, getReq_graftTwoLevel_son hc]
      simp only [dif_pos hc]
      exact grayTailSonRequest_mono (grayTailThreshold_le_eps q e) ⟨i, hi⟩ ⟨c, hc⟩ (hbase ⟨c, hc⟩)
    · have hc' : b ≤ c := not_lt.mp hc
      rw [getReq_graftTwoLevel_of_ge hc', getReq_graftTwoLevel_of_ge hc']
  · by_cases hc : c < b
    · by_cases hc' : c' < b
      · rw [getReq_graftTwoLevel_grandson hc hc', getReq_graftTwoLevel_grandson hc hc']
        simp only [dif_pos hc, dif_pos hc']
        exact hentry (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) y
      · have hc'' : b ≤ c' := not_lt.mp hc'
        rw [getReq_graftTwoLevel_of_son_ge hc hc'', getReq_graftTwoLevel_of_son_ge hc hc'']
    · have hc'' : b ≤ c := not_lt.mp hc
      rw [getReq_graftTwoLevel_of_ge hc'', getReq_graftTwoLevel_of_ge hc'']

/-- A step that freezes a round does not decrease the displayed request at any node. -/
lemma grayTailOutput_step_mono_of_goal_true
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) {st : GrayTailState n (grayTailBranch q L a e)}
    (hcert : GrayTailCertified q L e A sm t st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t)) = true)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayTailOutput q L a e sigma st) i x ≤
      getFamilyReq
        (grayTailOutput q L a e sigma (grayTailStep q L a e sigma A st (sm t))) i x := by
  have hnot_done : st.done = false := by
    cases hd : st.done <;> [rfl; simp [hd] at hdone_empty]
  set st' := grayTailStep q L a e sigma A st (sm t)
  have hentries : grayTailOutputEntries q L e sigma st' =
      grayTailOutputEntries q L e sigma st ++
        grayTailSlotEntries st'.slots (if st'.done then [] else grayTailCurrentMove q L e
                                        sigma st') :=
    grayTailOutputEntries_step_of_goal_true (a := a) (A := A) hdone_empty hgoal
  have hdone_mono : st.done = true → st'.done = true := by
    intro hd; rw [hd] at hnot_done; contradiction
  have hhist' := grayTailHistoryOK_step q L a e sigma A st (sm t) hhist
  have htrace' := grayTailTrace_step (a := a) (A := A) (t := t) (sm := sm) sigma htrace
  have hround' : st'.done = false →
      st'.frozen.length < grayTailRoundCount q := by
    intro hdone'
    by_contra hlt
    push_neg at hlt
    simp only [st', grayTailStep_eq_of_goal_true hdone_empty hgoal] at hlt
    have hcap : grayTailRoundCount q ≤ st.frozen.length + 1 := by
      simpa using hlt
    have hdone_true : st'.done = true := by
      simp [st', grayTailStep_eq_of_goal_true hdone_empty hgoal, hcap]
    rw [hdone_true] at hdone'
    contradiction
  have hbase_mono : ∀ c : Fin (grayTailBranch q L a e),
      grayTailSonBase (grayTailOutputEntries q L e sigma st) ⟨i, hi⟩ c ≤
        grayTailSonBase (grayTailOutputEntries q L e sigma st') ⟨i, hi⟩ c := by
    intro c
    rw [hentries, grayTailSonBase_append_globalEntries]
    have hnonneg : 0
      ≤ grayTailSonBase (grayTailSlotEntries st'.slots (if st'.done then [] else grayTailCurrentMove
                                                         q L e sigma st')) ⟨i, hi⟩ c := by
      refine grayTailSonBase_slotEntries_nonneg st'.slots (if st'.done then [] else
                                                            grayTailCurrentMove q L e sigma st')
        ?_ ⟨i, hi⟩ c
      intro j hj
      exact getReq_currentMove_nonneg ha hae hB hRung sm hsm (t + 1)
        (grayTailCertified_step (a := a) sigma hcert) hhist' htrace' hround' j hj []
    linarith
  have hentry_mono : ∀ (slot : GrayTailSlot n (grayTailBranch q L a e)) (y : GacsDayNode),
      getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st) slot) y ≤
        getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st') slot) y := by
    intro slot y
    rw [hentries]
    refine grayTailEntryMove_mono_append _ _ ?_ slot y
    intro pr hpr y'
    refine getReq_slotEntries_mem_nonneg st'.slots (if st'.done then [] else grayTailCurrentMove q L
                                                     e sigma st') ?_ pr hpr y'
    intro j hj y''
    exact getReq_currentMove_nonneg ha hae hB hRung sm hsm (t + 1)
      (grayTailCertified_step (a := a) sigma hcert) hhist' htrace' hround' j hj y''
  exact getFamilyReq_grayTailOutput_mono a hi x hdone_mono hbase_mono hentry_mono

/-- A step that misses the goal does not decrease the displayed request at any node. -/
lemma grayTailOutput_step_mono_of_goal_false
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) {st : GrayTailState n (grayTailBranch q L a e)}
    (hcert : GrayTailCertified q L e A sm t st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hround : st.frozen.length < grayTailRoundCount q)
    (hdone_empty : (st.done || st.slots.isEmpty) = false)
    (hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t)) = false)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayTailOutput q L a e sigma st) i x ≤
      getFamilyReq
        (grayTailOutput q L a e sigma (grayTailStep q L a e sigma A st (sm t))) i x := by
  have hnot_done : st.done = false := by
    cases hd : st.done <;> [rfl; simp [hd] at hdone_empty]
  set st' := grayTailStep q L a e sigma A st (sm t)
  have hdone_empty_ne : (st.done || st.slots.isEmpty) ≠ true := by
    rw [hdone_empty]; exact Bool.false_ne_true
  have hb : grayTailBaseBranch q L ≤ grayTailBranch q L a e := le_max_right _ _
  have hspec := grayTailRound_gameSpec ha hae hB hRung hcert hdone_empty_ne hb
  have hfs_legal := grayTailFutureServer_legal hcert hround hsm
  have hlegal := hspec.weak.legal (grayTailFutureServer q L e st sm) hfs_legal
  have hhist' := grayTailHistoryOK_step q L a e sigma A st (sm t) hhist
  have htrace' := grayTailTrace_step (a := a) (A := A) (t := t) (sm := sm) sigma htrace
  have hmove : ∀ j < st.slots.length, ∀ y,
      getReq (familyClientMoveAt (grayTailCurrentMove q L e sigma st) j) y ≤
        getReq (familyClientMoveAt (grayTailCurrentMove q L e sigma st') j) y := by
    intro j hj y
    have hcurr : grayTailCurrentMove q L e sigma st =
        playClientFamily st.unavailable st.slots.length
          (grayTailRoundStrategy q L e sigma st)
          (grayTailFutureServer q L e st sm) st.history.2.length :=
      grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace
    have hcurr' : grayTailCurrentMove q L e sigma st' =
        playClientFamily st.unavailable st.slots.length
          (grayTailRoundStrategy q L e sigma st)
          (grayTailFutureServer q L e st sm) (st.history.2.length + 1) := by
      simpa [st', grayTailStep_eq_of_goal_false hdone_empty hgoal] using
        (grayTailCurrentMove_eq_futurePlay q L e sigma hhist' htrace')
    rw [hcurr, hcurr']
    exact hlegal.2 st.history.2.length j hj y
  have hcur : (if st.done then [] else grayTailCurrentMove q L e sigma st) =
      grayTailCurrentMove q L e sigma st := by simp [hnot_done]
  have hdone_mono : st.done = true → st'.done = true := by
    intro hd; rw [hd] at hnot_done; contradiction
  have hentries : grayTailOutputEntries q L e sigma st' =
      grayTailEntries st.frozen st.slots (grayTailCurrentMove q L e sigma st') :=
    grayTailOutputEntries_step_of_goal_false hdone_empty hgoal
  have hbase_mono : ∀ c : Fin (grayTailBranch q L a e),
      grayTailSonBase (grayTailOutputEntries q L e sigma st) ⟨i, hi⟩ c ≤
        grayTailSonBase (grayTailOutputEntries q L e sigma st') ⟨i, hi⟩ c := by
    intro c
    rw [hentries]
    have hst_entries : grayTailOutputEntries q L e sigma st =
        grayTailEntries st.frozen st.slots (grayTailCurrentMove q L e sigma st) := by
      unfold grayTailOutputEntries; rw [hcur]
    rw [hst_entries]
    unfold grayTailEntries
    rw [grayTailSonBase_append_globalEntries, grayTailSonBase_append_globalEntries]
    gcongr
    exact grayTailSonBase_slotEntries_mono st.slots
      (grayTailCurrentMove q L e sigma st) (grayTailCurrentMove q L e sigma st')
      (fun j hj => hmove j hj []) ⟨i, hi⟩ c
  have hentry_mono : ∀ (slot : GrayTailSlot n (grayTailBranch q L a e)) (y : GacsDayNode),
      getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st) slot) y ≤
        getReq (grayTailEntryMove (grayTailOutputEntries q L e sigma st') slot) y := by
    intro slot y
    rw [hentries]
    have hst_entries : grayTailOutputEntries q L e sigma st =
        grayTailEntries st.frozen st.slots (grayTailCurrentMove q L e sigma st) := by
      unfold grayTailOutputEntries; rw [hcur]
    rw [hst_entries]
    exact grayTailEntryMove_mono_append_of_frozen _ st.slots
      (grayTailCurrentMove q L e sigma st) (grayTailCurrentMove q L e sigma st')
      hmove slot y
  exact getFamilyReq_grayTailOutput_mono a hi x hdone_mono hbase_mono hentry_mono

/-- Along a certified run against a legal server play, one tail step never decreases the
displayed request at any node. -/
theorem grayTailOutput_step_mono
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) {st : GrayTailState n (grayTailBranch q L a e)}
    (hcert : GrayTailCertified q L e A sm t st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hround : (st.done || st.slots.isEmpty) = false →
        st.frozen.length < grayTailRoundCount q)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayTailOutput q L a e sigma st) i x ≤
      getFamilyReq
        (grayTailOutput q L a e sigma (grayTailStep q L a e sigma A st (sm t))) i x := by
  by_cases hde : (st.done || st.slots.isEmpty) = true
  · exact grayTailOutput_step_mono_of_done_or_slots_empty sm t st hde i hi x
  · have hde_false : (st.done || st.slots.isEmpty) = false := by
      cases h : (st.done || st.slots.isEmpty)
      · rfl
      · contradiction
    by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t)) = true
    · exact grayTailOutput_step_mono_of_goal_true ha hae hB hRung sm hsm t hcert hhist htrace
        hde_false hg i hi x
    · have hg_false : familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm t)) = false := by
        cases h : familyRobustGrayGoalAtB _ _ _ _ _ _ _ _
        · rfl
        · contradiction
      exact grayTailOutput_step_mono_of_goal_false ha hae hB hRung sm hsm t hcert hhist htrace
        (hround hde_false) hde_false hg_false i hi x

/-- **Child E5f.**  The displayed outer requests never decrease in the outer
time.  Requests only change when a round freezes, and freezing can only replace
a son base by a larger one or raise it to `dyadicScale e`; the terminal root
adjustment is a `max` with the previous value. -/
theorem grayTail_output_monotone
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (playClientFamily A n (grayTailStrategy q L a e sigma) sm t) i x ≤
      getFamilyReq
        (playClientFamily A n (grayTailStrategy q L a e sigma) sm (t + 1)) i x := by
  rw [playClientFamily_grayTailStrategy q L a e n sigma A sm t,
    playClientFamily_grayTailStrategy q L a e n sigma A sm (t + 1),
    grayTailStateAt_succ]
  exact grayTailOutput_step_mono ha hae hB hRung sm hsm t
    (grayTailCertified_stateAt q L a e sigma A sm t)
    (grayTailHistoryOK_stateAt q L a e sigma A sm t)
    (grayTailTrace_stateAt q L a e sigma A sm t)
    (fun hactive => by
      by_contra h
      push_neg at h
      have hdone := grayTail_done_of_roundCount_stateAt_core
        (q := q) (L := L) (a := a) (e := e)
        (sigma := sigma) (A := A) (sm := sm) (t := t) h
      apply Bool.false_ne_true
      calc
        false = ((grayTailStateAt (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).done ||
          (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).slots.isEmpty) := hactive.symm
        _ = true := by simp [hdone])
    i hi x

/-- The target floor of the tail is at least the fine scale
`dyadicScale (e + grayTailNewLoss q L)`. -/
theorem grayTailTargetFloor_avoidsSmall (q L a e : ℕ)
    (_ha : 1 ≤ a) (hae : a ≤ e) :
    dyadicScale (e + grayTailNewLoss q L) ≤ grayTailTargetFloor q a := by
  have hloss_ge : 256 * (q + 1) ≤ 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := by omega
  have hdepth_ge : a + 256 * (q + 1) ≤ e + grayTailNewLoss q L := by
    unfold grayTailNewLoss; omega
  have hscale_le : dyadicScale (e + grayTailNewLoss q L) ≤ dyadicScale (a + 256 * (q + 1)) :=
    dyadicScale_antitone hdepth_ge
  refine le_trans hscale_le ?_
  unfold grayTailTargetFloor halfAmplification dyadicScale
  rw [pow_add]
  have hpos : 0 < (1 / 2 : ℚ) ^ a := by positivity
  push_cast
  have hmul : (1 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (256 * (q + 1)) ≤
      ((3 / 4 : ℚ) * (1 / 2 : ℚ) ^ a) / (1 + ((q : ℚ) + 1) / 2) ↔
      (1 / 2 : ℚ) ^ (256 * (q + 1)) ≤ (3 / 4 : ℚ) / (1 + ((q : ℚ) + 1) / 2) := by
    constructor
    · intro h
      have h1 : (1 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (256 * (q + 1)) ≤
          (1 / 2 : ℚ) ^ a * ((3 / 4 : ℚ) / (1 + ((q : ℚ) + 1) / 2)) := by
        calc (1 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (256 * (q + 1))
          _ ≤ ((3 / 4 : ℚ) * (1 / 2 : ℚ) ^ a) / (1 + ((q : ℚ) + 1) / 2) := h
          _ = (1 / 2 : ℚ) ^ a * ((3 / 4 : ℚ) / (1 + ((q : ℚ) + 1) / 2)) := by ring
      exact (mul_le_mul_iff_of_pos_left hpos).mp h1
    · intro h
      calc (1 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (256 * (q + 1))
        _ ≤ (1 / 2 : ℚ) ^ a * ((3 / 4 : ℚ) / (1 + ((q : ℚ) + 1) / 2)) :=
          mul_le_mul_of_nonneg_left h hpos.le
        _ = ((3 / 4 : ℚ) * (1 / 2 : ℚ) ^ a) / (1 + ((q : ℚ) + 1) / 2) := by ring
  rw [hmul]
  have hpow_q : (1 / 2 : ℚ) ^ (256 * (q + 1)) = 1 / (2 : ℚ) ^ (256 * (q + 1)) := by simp
  rw [hpow_q]
  have hpow_nat : 2 * (q + 3) ≤ 3 * 2 ^ (256 * (q + 1)) := by
    have h1 : q + 3 ≤ 2 ^ (256 * (q + 1)) := by
      calc q + 3
        _ ≤ 2 ^ (q + 3) := Nat.le_two_pow_self (q + 3)
        _ ≤ 2 ^ (256 * (q + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h2pow_pos : 0 < (2 : ℚ) ^ (256 * (q + 1)) := by positivity
  have hden_pos : 0 < 2 * ((q : ℚ) + 3) := by linarith
  have hfrac : (3 / 4 : ℚ) / (1 + ((q : ℚ) + 1) / 2) = 3 / (2 * ((q : ℚ) + 3)) := by
    have hq_den : (1 : ℚ) + ((q : ℚ) + 1) / 2 = ((q : ℚ) + 3) / 2 := by ring
    rw [hq_den]
    calc (3 / 4 : ℚ) / (((q : ℚ) + 3) / 2)
      _ = (3 / 4 * 2 : ℚ) / ((q : ℚ) + 3) := div_div_eq_mul_div _ _ _
      _ = (3 / 2 : ℚ) / ((q : ℚ) + 3) := by norm_num
      _ = 3 / (2 * ((q : ℚ) + 3)) := div_div 3 2 _
  rw [hfrac]
  rw [div_le_div_iff₀ h2pow_pos hden_pos]
  have hpow_nat_cast : 2 * (q : ℚ) + 6 ≤ 3 * (2 : ℚ) ^ (256 * (q + 1)) := by
    exact_mod_cast hpow_nat
  linarith

/-- For nonnegative rational terms each either zero or at least `delta`, a positive
sum is at least `delta`. -/
lemma sum_ge_of_forall_zero_or_ge {α : Type*} (s : Finset α) (f : α → ℚ) (delta : ℚ)
    (hpos : 0 < ∑ x ∈ s, f x)
    (hbound : ∀ x ∈ s, f x = 0 ∨ delta ≤ f x) :
    delta ≤ ∑ x ∈ s, f x := by
  by_cases hd : delta ≤ 0
  · linarith
  · push_neg at hd
    have hnonneg : ∀ y ∈ s, 0 ≤ f y := by
      intro y hy
      rcases hbound y hy with h0 | hge
      · rw [h0]
      · linarith
    have hexists : ∃ x ∈ s, f x ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hzero : ∑ x ∈ s, f x = 0 := Finset.sum_eq_zero hnone
      linarith
    obtain ⟨x, hx, hnz⟩ := hexists
    have hge_delta : delta ≤ f x := by
      rcases hbound x hx with h0 | hge
      · contradiction
      · exact hge
    have hle_sum : f x ≤ ∑ x ∈ s, f x := Finset.single_le_sum hnonneg hx
    exact le_trans hge_delta hle_sum

end Kolmogorov
