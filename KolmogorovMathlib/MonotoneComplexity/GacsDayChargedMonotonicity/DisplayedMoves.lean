import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.RootIncrements
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.AvoidsSmall
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields

/-!
# One step of the charged outer run: the monotonicity lemmas

The displayed move of the charged run is a graft of the entry table of the run's state.  This
module collects the lemmas that compare the displayed moves of two states: monotonicity in the
son bases and the entry moves, in an appended entry table, and along a history-extending step.
The phase analysis that applies them to consecutive states of a run is in the parent module.
-/

namespace Kolmogorov

/-- The service threshold is below the scale it approximates: `grayChargedThreshold q e` is at
most `dyadicScale e`. -/
lemma grayChargedThreshold_le_eps (q e : Nat) :
    grayChargedThreshold q e <= dyadicScale e := by
  unfold grayChargedThreshold
  have hnonneg : 0 <=
      dyadicScale e / (6 * halfAmplification q) :=
    div_nonneg (dyadicScale_pos e).le (by
      unfold halfAmplification
      positivity)
  linarith

/-- The son request is monotone in the son base of that child, as long as the threshold does not
exceed the scale. -/
lemma grayChargedSonRequest_mono {n b : Nat}
    {source : Nat} {threshold eps : Rat}
    (htheps : threshold <= eps)
    {entries1 entries2 : List (GrayTailSlot n b × ClientMove)}
    (i : Fin n) (c : Fin b)
    (hbase : grayTailSonBase entries1 i c <=
      grayTailSonBase entries2 i c) :
    grayChargedSonRequest source threshold eps entries1 i c <=
      grayChargedSonRequest source threshold eps entries2 i c := by
  unfold grayChargedSonRequest
  by_cases hc : c.val < source
  · simp only [hc, ite_true]
    exact grayTailSonRequest_mono htheps i c hbase
  · simp only [hc, ite_false]
    exact hbase

/-- The displayed move is monotone in its entries: growing every son base and every entry move
grows the request at every node. -/
lemma getFamilyReq_grayChargedDisplayedMove_mono
    {q L a e n b i : Nat} {sigma : FamilyStrategyScheme}
    {st1 st2 : GrayChargedState n b} (hi : i < n) (x : GacsDayNode)
    (hbase : forall c : Fin b,
      grayTailSonBase (grayChargedOutputEntries q L a e sigma st1) ⟨i, hi⟩ c <=
        grayTailSonBase (grayChargedOutputEntries q L a e sigma st2) ⟨i, hi⟩ c)
    (hentry : forall (slot : GrayTailSlot n b) (y : GacsDayNode),
      getReq (grayTailEntryMove
        (grayChargedOutputEntries q L a e sigma st1) slot) y <=
      getReq (grayTailEntryMove
        (grayChargedOutputEntries q L a e sigma st2) slot) y) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st1) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma st2) i x := by
  change getReq
      (familyClientMoveAt (grayChargedDisplayedMove q L a e sigma st1) i) x <=
    getReq
      (familyClientMoveAt (grayChargedDisplayedMove q L a e sigma st2) i) x
  unfold grayChargedDisplayedMove grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left hi, dite_eq_left hi]
  simp only [Option.getD_some]
  rcases x with _ | ⟨c, _ | ⟨c', y⟩⟩
  · rw [getReq_graftTwoLevel_root, getReq_graftTwoLevel_root]
    unfold grayChargedRootRequest
    exact Finset.sum_le_sum fun c _ =>
      grayChargedSonRequest_mono (grayChargedThreshold_le_eps q e)
        ⟨i, hi⟩ c (hbase c)
  · by_cases hc : c < b
    · rw [getReq_graftTwoLevel_son hc, getReq_graftTwoLevel_son hc]
      simp only [dite_eq_left hc]
      exact grayChargedSonRequest_mono (grayChargedThreshold_le_eps q e)
        ⟨i, hi⟩ ⟨c, hc⟩ (hbase ⟨c, hc⟩)
    · have hc' : b <= c := Nat.le_of_not_gt hc
      rw [getReq_graftTwoLevel_of_ge hc', getReq_graftTwoLevel_of_ge hc']
  · by_cases hc : c < b
    · by_cases hc' : c' < b
      · rw [getReq_graftTwoLevel_grandson hc hc',
          getReq_graftTwoLevel_grandson hc hc']
        simp only [dite_eq_left hc, dite_eq_left hc']
        exact hentry (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) y
      · have hc'' : b <= c' := Nat.le_of_not_gt hc'
        rw [getReq_graftTwoLevel_of_son_ge hc hc'',
          getReq_graftTwoLevel_of_son_ge hc hc'']
    · have hc'' : b <= c := Nat.le_of_not_gt hc
      rw [getReq_graftTwoLevel_of_ge hc'', getReq_graftTwoLevel_of_ge hc'']

/-- Appending nonnegative entries to a charged state only increases the requests it displays. -/
lemma getFamilyReq_grayChargedDisplayedMove_mono_append
    {q L a e n b i : Nat} {sigma : FamilyStrategyScheme}
    {st1 st2 : GrayChargedState n b} (hi : i < n) (x : GacsDayNode)
    {newEntries : List (GrayTailSlot n b × ClientMove)}
    (hentries : grayChargedOutputEntries q L a e sigma st2 =
      grayChargedOutputEntries q L a e sigma st1 ++ newEntries)
    (hnonneg : forall pr, pr ∈ newEntries -> forall y, 0 <= getReq pr.2 y) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st1) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma st2) i x := by
  apply getFamilyReq_grayChargedDisplayedMove_mono hi x
  · intro c
    rw [hentries, grayTailSonBase_append_globalEntries]
    exact le_add_of_nonneg_right
      (grayTailSonBase_nonneg_global (entries := newEntries) (i := ⟨i, hi⟩)
        (c := c) (fun pr hpr => hnonneg pr hpr []))
  · intro slot y
    rw [hentries]
    exact grayTailEntryMove_mono_append _ _ hnonneg slot y

/-- Two states with the same frozen rounds and slots display requests ordered as their current
moves are. -/
lemma getFamilyReq_grayChargedDisplayedMove_mono_current
    {q L a e n b i : Nat} {sigma : FamilyStrategyScheme}
    {st1 st2 : GrayChargedState n b} (hi : i < n) (x : GacsDayNode)
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {move1 move2 : FamilyClientMove}
    (hentries1 : grayChargedOutputEntries q L a e sigma st1 =
      grayTailEntries frozen slots move1)
    (hentries2 : grayChargedOutputEntries q L a e sigma st2 =
      grayTailEntries frozen slots move2)
    (hmove : forall j, j < slots.length -> forall y,
      getReq (familyClientMoveAt move1 j) y <=
        getReq (familyClientMoveAt move2 j) y) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st1) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma st2) i x := by
  apply getFamilyReq_grayChargedDisplayedMove_mono hi x
  · intro c
    rw [hentries1, hentries2]
    unfold grayTailEntries
    rw [grayTailSonBase_append_globalEntries, grayTailSonBase_append_globalEntries]
    gcongr
    exact grayTailSonBase_slotEntries_mono slots move1 move2
      (fun j hj => hmove j hj []) ⟨i, hi⟩ c
  · intro slot y
    rw [hentries1, hentries2]
    exact grayTailEntryMove_mono_append_of_frozen frozen slots
      move1 move2 hmove slot y

/-- Extending the history by one round only increases the current advantage move: in every slot
and at every node, the request afterwards is at least the request before. -/
lemma grayChargedCurrentMove_mono_of_legal
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hlocal : familyServerPlayLegal st.slots.length
      (grayTailBranch q L a e) st.unavailable
      (grayTailFutureServer q L e st sm))
    (hne : 1 <= st.slots.length) :
    let current := grayTailCurrentMove q L e sigma st
    let localSM := grayTailLocalServerMove
      (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)
    let st' : GrayTailState n (grayTailBranch q L a e) :=
      { st with
        time := st.time + 1
        history := (st.history.1 ++ [current], st.history.2 ++ [localSM]) }
    GrayTailHistoryOK q L e sigma st' ->
    GrayTailTrace q L e sm (t + 1) st' ->
    forall j, j < st.slots.length -> forall y,
      getReq (familyClientMoveAt current j) y <=
        getReq (familyClientMoveAt
          (grayTailCurrentMove q L e sigma st') j) y := by
  dsimp only
  intro hhist' htrace' j hj y
  have hcall : 1 <= grayCallDepth q e := by
    unfold grayCallDepth
    omega
  have heps : grayCallDepth q e <=
      grayTailRoundEps q L e st.frozen.length :=
    grayTailRoundEps_lower q L e st.frozen.length
  have hbranch :
      ladderBranching B (grayCallDepth q e)
          (grayTailRoundEps q L e st.frozen.length) <=
        grayTailBranch q L a e :=
    le_trans (grayTailRecursiveBranch_le hB) (le_max_right _ _)
  have hspec := grayFamilyGameSpec_mono_branching hbranch
    (hRung (grayCallDepth q e)
      (grayTailRoundEps q L e st.frozen.length)
      hcall heps st.slots.length st.unavailable hne).weak
  have hlegal := hspec.legal (grayTailFutureServer q L e st sm) hlocal
  have hcurr := grayTailCurrentMove_eq_futurePlay
    q L e sigma hhist htrace
  have hcurr' := grayTailCurrentMove_eq_futurePlay
    q L e sigma hhist' htrace'
  have hlegal2 := hlegal.2 st.history.2.length j hj y
  have heq1 : familyClientMoveAt (grayTailCurrentMove q L e sigma st) j = 
      familyClientMoveAt (playClientFamily st.unavailable st.slots.length
        (sigma (grayCallDepth q e) (grayTailRoundEps q L e st.frozen.length))
        (grayTailFutureServer q L e st sm) st.history.2.length) j := by
    rw [hcurr]
    rfl
  have heq2 : familyClientMoveAt (grayTailCurrentMove q L e sigma
          { time := st.time + 1, roundStart := st.roundStart, done := st.done, frozen := st.frozen,
            unavailable := st.unavailable, slots := st.slots, anchoringSlots := st.anchoringSlots,
            history :=
              (st.history.1 ++ [grayTailCurrentMove q L e sigma st],
                st.history.2 ++
                  [grayTailLocalServerMove (grayTailRoundDelta q L e (List.length st.frozen))
                    st.slots (sm t)]) }) j = 
      familyClientMoveAt (playClientFamily st.unavailable st.slots.length
        (sigma (grayCallDepth q e) (grayTailRoundEps q L e st.frozen.length))
        (grayTailFutureServer q L e st sm) (st.history.2.length + 1)) j := by
    rw [hcurr']
    unfold grayTailRoundStrategy grayTailFutureServer
    dsimp only
    have h_len : (st.history.2 ++
      [grayTailLocalServerMove (grayTailRoundDelta q L e (List.length st.frozen))
        st.slots (sm t)]).length =
      st.history.2.length + 1 := by simp
    rw [h_len]
  have hc1 := congrArg (fun m => getReq m y) heq1
  have hc2 := congrArg (fun m => getReq m y) heq2
  rw [hc1, hc2]
  exact hlegal2

/-- Extending the history by one round only increases the spend move of the pass: in every slot
and at every node, the request afterwards is at least the request before. -/
lemma grayChargedSpendMove_mono_of_legal
    {q L B a e n t pass : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove}
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hhist : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass, core := st })
    (htrace : GrayTailTraceAt (grayChargedSpendDelta a L e pass) sm t st)
    (hlocal : familyServerPlayLegal st.slots.length
      (grayTailBranch q L a e) st.unavailable
      (grayChargedSpendFutureServer a L e pass st sm))
    (hne : 1 <= st.slots.length) :
    let current := grayChargedSpendMove q L a e pass sigma st
    let localSM := grayTailLocalServerMove
      (grayChargedSpendDelta a L e pass) st.slots (sm t)
    let st' : GrayTailState n (grayTailBranch q L a e) :=
      { st with
        time := st.time + 1
        history := (st.history.1 ++ [current], st.history.2 ++ [localSM]) }
    GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass, core := st' } ->
    GrayTailTraceAt (grayChargedSpendDelta a L e pass) sm (t + 1) st' ->
    forall j, j < st.slots.length -> forall y,
      getReq (familyClientMoveAt current j) y <=
        getReq (familyClientMoveAt
          (grayChargedSpendMove q L a e pass sigma st') j) y := by
  dsimp only
  intro hhist' htrace' j hj y
  have hspec := grayFamilyGameSpec_mono_branching
    (grayChargedSpendBranch_le pass hB)
    (hRung (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass)
      (by unfold grayChargedSpendAlphaDepth; omega)
      (le_max_left _ _) st.slots.length st.unavailable hne).weak
  have hlegal := hspec.legal
    (grayChargedSpendFutureServer a L e pass st sm) hlocal
  have hcurr := grayChargedSpendMove_eq_futurePlay
    q L a e pass sigma hhist htrace
  have hcurr' := grayChargedSpendMove_eq_futurePlay
    q L a e pass sigma hhist' htrace'
  have hlegal2 := hlegal.2 st.history.2.length j hj y
  have heq1 : familyClientMoveAt (grayChargedSpendMove q L a e pass sigma st) j = 
      familyClientMoveAt (playClientFamily st.unavailable st.slots.length
        (sigma (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass))
        (grayChargedSpendFutureServer a L e pass st sm) st.history.2.length) j := by
    rw [hcurr]
    rfl
  have heq2 : familyClientMoveAt (grayChargedSpendMove q L a e pass sigma
          { time := st.time + 1, roundStart := st.roundStart, done := st.done,
            frozen := st.frozen, unavailable := st.unavailable, slots := st.slots,
            anchoringSlots := st.anchoringSlots,
            history :=
              (st.history.1 ++ [grayChargedSpendMove q L a e pass sigma st],
                st.history.2 ++
                  [grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                    st.slots (sm t)]) }) j = 
      familyClientMoveAt (playClientFamily st.unavailable st.slots.length
        (sigma (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass))
        (grayChargedSpendFutureServer a L e pass st sm) (st.history.2.length + 1)) j := by
    rw [hcurr']
    dsimp only [grayChargedRoundStrategy, grayChargedSpendFutureServer]
    have h_len : (st.history.2 ++
      [grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots (sm t)]).length =
      st.history.2.length + 1 := by simp
    rw [h_len]
    rfl
  have hc1 := congrArg (fun m => getReq m y) heq1
  have hc2 := congrArg (fun m => getReq m y) heq2
  rw [hc1, hc2]
  exact hlegal2

/-- In the `advantage` phase of a run against a legal server play, every slot entry of the
current move requests a nonnegative amount at every node. -/
lemma grayChargedCurrentSlotEntries_stateAt_nonneg
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hadv :
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage)
    (hnonempty :
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.isEmpty = false) :
    forall pr,
      pr ∈ grayTailSlotEntries
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots
        (grayTailCurrentMove q L e sigma
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) ->
      forall y, 0 <= getReq pr.2 y := by
  have hlen : 1 <=
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length := by
    have hpos : 0 <
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots.length := by
      by_contra hz
      have hzero :
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots.length = 0 :=
        Nat.eq_zero_of_not_pos hz
      have hempty :
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots = [] :=
        List.length_eq_zero_iff.mp hzero
      simp [hempty] at hnonempty
    omega
  have hcoh := grayChargedCurrentMove_stateAt_coherent
    (t := t) ha hae hB hRung hsm hadv hlen
  intro pr hpr y
  exact getReq_slotEntries_mem_nonneg _ _
    (fun j hj y' => (hcoh j hj).1 y') pr hpr y

/-- In a spend pass of a run against a legal server play, every slot entry of the spend move
requests a nonnegative amount at every node. -/
lemma grayChargedSpendSlotEntries_stateAt_nonneg
    {q L B a e n t pass : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hphase :
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .spend pass)
    (hnonempty :
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.isEmpty = false) :
    forall pr,
      pr ∈ grayTailSlotEntries
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots
        (grayChargedSpendMove q L a e pass sigma
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) ->
      forall y, 0 <= getReq pr.2 y := by
  have hlen : 1 <=
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length := by
    have hpos : 0 <
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots.length := by
      by_contra hz
      have hzero :
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots.length = 0 :=
        Nat.eq_zero_of_not_pos hz
      have hempty :
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots = [] :=
        List.length_eq_zero_iff.mp hzero
      simp [hempty] at hnonempty
    omega
  have hcoh := grayChargedSpendMove_stateAt_coherent
    (t := t) hroom hB hRung hsm pass hphase hlen
  intro pr hpr y
  exact getReq_slotEntries_mem_nonneg _ _
    (fun j hj y' => (hcoh j hj).1 y') pr hpr y

/-- A step that only extends the history of the `advantage` phase does not decrease the displayed
request at any node. -/
lemma grayChargedDisplayedMove_step_mono_of_history
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (st : GrayChargedState n (grayTailBranch q L a e))
    (htail : GrayChargedTailCertified q L e A sm t st.core)
    (hround : st.core.frozen.length < grayTailRoundCount q)
    (hhist : GrayTailHistoryOK q L e sigma st.core)
    (htrace : GrayTailTrace q L e sm t st.core)
    (hslots : st.core.slots.isEmpty = false)
    (hstep : grayChargedStep q L a e sigma A st (sm t) =
      { phase := st.phase
        core :=
          { st.core with
            time := st.core.time + 1
            history :=
              (st.core.history.1 ++
                [grayTailCurrentMove q L e sigma st.core],
               st.core.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.core.frozen.length)
                  st.core.slots (sm t)]) } })
    (hhist' : GrayTailHistoryOK q L e sigma
      (grayChargedStep q L a e sigma A st (sm t)).core)
    (htrace' : GrayTailTrace q L e sm (t + 1)
      (grayChargedStep q L a e sigma A st (sm t)).core)
    (hentries1 : grayChargedOutputEntries q L a e sigma st =
      grayTailEntries st.core.frozen st.core.slots
        (grayTailCurrentMove q L e sigma st.core))
    (hentries2 : grayChargedOutputEntries q L a e sigma
        (grayChargedStep q L a e sigma A st (sm t)) =
      grayTailEntries st.core.frozen st.core.slots
        (grayTailCurrentMove q L e sigma
          (grayChargedStep q L a e sigma A st (sm t)).core))
    (i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st) i x <=
      getFamilyReq
        (grayChargedDisplayedMove q L a e sigma
          (grayChargedStep q L a e sigma A st (sm t))) i x := by
  have hne : 1 <= st.core.slots.length := by
    have hpos : 0 < st.core.slots.length := by
      by_contra hz
      have hzero : st.core.slots.length = 0 := Nat.eq_zero_of_not_pos hz
      have hempty : st.core.slots = [] := List.length_eq_zero_iff.mp hzero
      simp [hempty] at hslots
    omega
  have hlocal := grayChargedCoreFutureServer_legal_outer
    htail hround hsm
  rw [hstep] at hhist' htrace'
  have hmove := grayChargedCurrentMove_mono_of_legal
    ha hae hB hRung st.core hhist htrace hlocal hne hhist' htrace'
  rw [hstep] at hentries2 ⊢
  exact getFamilyReq_grayChargedDisplayedMove_mono_current hi x
    hentries1 hentries2 hmove

/-- A step that only extends the history of a spend pass does not decrease the displayed request
at any node. -/
lemma grayChargedDisplayedMove_step_mono_of_history_spend
    {q L B a e n t pass : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayChargedState n (grayTailBranch q L a e))
    (hhist : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass, core := st.core })
    (htrace : GrayTailTraceAt (grayChargedSpendDelta a L e pass)
      sm t st.core)
    (hlocal : familyServerPlayLegal st.core.slots.length
      (grayTailBranch q L a e) st.core.unavailable
      (grayChargedSpendFutureServer a L e pass st.core sm))
    (hslots : st.core.slots.isEmpty = false)
    (hstep : grayChargedStep q L a e sigma A st (sm t) =
      { phase := st.phase
        core :=
          { st.core with
            time := st.core.time + 1
            history :=
              (st.core.history.1 ++
                [grayChargedSpendMove q L a e pass sigma st.core],
               st.core.history.2 ++
                [grayTailLocalServerMove
                  (grayChargedSpendDelta a L e pass)
                  st.core.slots (sm t)]) } })
    (hhist' : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass,
        core := (grayChargedStep q L a e sigma A st (sm t)).core })
    (htrace' : GrayTailTraceAt (grayChargedSpendDelta a L e pass)
      sm (t + 1) (grayChargedStep q L a e sigma A st (sm t)).core)
    (hentries1 : grayChargedOutputEntries q L a e sigma st =
      grayTailEntries st.core.frozen st.core.slots
        (grayChargedSpendMove q L a e pass sigma st.core))
    (hentries2 : grayChargedOutputEntries q L a e sigma
        (grayChargedStep q L a e sigma A st (sm t)) =
      grayTailEntries st.core.frozen st.core.slots
        (grayChargedSpendMove q L a e pass sigma
          (grayChargedStep q L a e sigma A st (sm t)).core))
    (i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st) i x <=
      getFamilyReq
        (grayChargedDisplayedMove q L a e sigma
          (grayChargedStep q L a e sigma A st (sm t))) i x := by
  have hne : 1 <= st.core.slots.length := by
    have hpos : 0 < st.core.slots.length := by
      by_contra hz
      have hzero : st.core.slots.length = 0 := Nat.eq_zero_of_not_pos hz
      have hempty : st.core.slots = [] := List.length_eq_zero_iff.mp hzero
      simp [hempty] at hslots
    omega
  rw [hstep] at hhist' htrace'
  have hmove := grayChargedSpendMove_mono_of_legal
    (t := t) hB hRung st.core hhist htrace hlocal hne hhist' htrace'
  rw [hstep] at hentries2 ⊢
  exact getFamilyReq_grayChargedDisplayedMove_mono_current hi x
    hentries1 hentries2 hmove

/-- A step that only appends nonnegative slot entries does not decrease the displayed request at
any node. -/
lemma grayChargedDisplayedMove_step_mono_of_append
    {q L a e n b i : Nat} {sigma : FamilyStrategyScheme}
    {st1 st2 : GrayChargedState n b} (hi : i < n) (x : GacsDayNode)
    {move2 : FamilyClientMove}
    (hentries : grayChargedOutputEntries q L a e sigma st2 =
      grayChargedOutputEntries q L a e sigma st1 ++
        grayTailSlotEntries st2.core.slots move2)
    (hnonneg : forall pr,
      pr ∈ grayTailSlotEntries st2.core.slots move2 ->
      forall y, 0 <= getReq pr.2 y) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma st1) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma st2) i x :=
  getFamilyReq_grayChargedDisplayedMove_mono_append hi x hentries hnonneg

end Kolmogorov
