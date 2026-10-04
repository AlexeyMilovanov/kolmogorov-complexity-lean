import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.CertifiedStates
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailGlobalProgress

/-!
# The charged tail step and the fields of the closure argument

The step-level facts about the charged controller that the closure of the charged strategy
consumes. `GrayChargedPositive` is the property to be established — the charged strategy wins the
`n`-client family game — and `grayChargedRunState`, `grayChargedRunMove` name the state and the
displayed move at an outer time, with `GrayChargedFinalAt` naming the last transition before the
controller enters `done`.

### Outline

* what a tail step does to the frozen rounds (`grayChargedTailStep_frozen_prefix`,
  `grayChargedStartSpend_frozen`) and to the other components of the state;
* the reachability hypotheses `GrayChargedSpendFutureLegal` and `GrayChargedSpendProgress`: the
  recursive server seen in a spend round is legal, and no reachable spend pass waits forever;
* `GrayChargedChargeGeometry` and `GrayChargedOuterFields`, which separate the geometric part of
  the final charge and the non-winning fields of the outer weak game specification from the
  numerical accounting.
-/



namespace Kolmogorov

/-- The charged strategy `grayChargedStrategy q L a e sigma` wins the `n`-client family game with
positive unserved mass, at branching `grayTailBranch q L a e` and slack `2 * (q + 1)`,
against the server play `sm`. -/
def GrayChargedPositive
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  familyClientWinsUnservedPositive n (2 * (q + 1))
    (grayTailBranch q L a e)
    (playClientFamily A n (grayChargedStrategy q L a e sigma) sm) sm

/-- The complete charged-controller state reconstructed at outer time `t`. -/
abbrev grayChargedRunState
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedState n (grayTailBranch q L a e) :=
  grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t

/-- The outer client move displayed by the charged controller at time `t`. -/
abbrev grayChargedRunMove
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : FamilyClientMove :=
  playClientFamily A n (grayChargedStrategy q L a e sigma) sm t

/-- A useful terminal time is the last transition time before the controller
enters `done`.  The done controller keeps displaying the frozen requests; only
its active recursive component is empty. -/
def GrayChargedFinalAt
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : Prop :=
  let st := grayChargedRunState q L a e n sigma A sm t
  st.phase ≠ .done ∧
    (grayChargedStep q L a e sigma A st (sm t)).phase = .done

/-- A charged tail step only appends to the frozen rounds: the earlier list stays a prefix. -/
lemma grayChargedTailStep_frozen_prefix {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (m : FamilyServerMove) :
    st.frozen <+:
      (grayChargedTailStep q L a e sigma A st m).frozen := by
  rw [grayChargedTailStep_eq]
  by_cases hterminal : (st.done || st.slots.isEmpty) = true
  · simp [hterminal]
  · simp only [hterminal]
    by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · simp [hgoal]
    · simp [hgoal]

/-- Opening a spend pass leaves the frozen rounds unchanged. -/
lemma grayChargedStartSpend_frozen {n b : Nat}
    (q L a e : Nat) (A : Allocation) (st : GrayTailState n b)
    (m : FamilyServerMove) :
    (grayChargedStartSpend q L a e A st m).core.frozen = st.frozen := by
  by_cases hslots : grayChargedSlotsForPass q a e 0 st.frozen = []
  · simp [grayChargedStartSpend, hslots]
  · simp [grayChargedStartSpend, hslots]

/-- A charged step only appends to the frozen rounds: the earlier list stays a prefix. -/
lemma grayChargedStep_frozen_prefix {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedState n b) (m : FamilyServerMove) :
    st.core.frozen <+:
      (grayChargedStep q L a e sigma A st m).core.frozen := by
  cases hphase : st.phase with
  | done => simp [grayChargedStep, hphase]
  | advantage =>
      simp only [grayChargedStep, hphase]
      let next := grayChargedTailStep q L a e sigma A st.core m
      by_cases hdone : next.done = true
      · have hprefix :=
          grayChargedTailStep_frozen_prefix q L a e sigma A st.core m
        have hdone' :
            (grayChargedTailStep q L a e sigma A st.core m).done = true := by
          simpa [next] using hdone
        rw [ite_eq_left hdone', grayChargedStartSpend_frozen]
        exact hprefix
      · simpa [next, hdone] using
          grayChargedTailStep_frozen_prefix q L a e sigma A st.core m
  | spend pass =>
      by_cases hslots : st.core.slots.isEmpty = true
      · simp [grayChargedStep, hphase, hslots]
      · let epsRound := grayChargedSpendEps a L e pass
        let deltaRound := grayChargedSpendDelta a L e pass
        let current := grayChargedSpendMove q L a e pass sigma st.core
        let localSM := grayTailLocalServerMove deltaRound st.core.slots m
        by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable current localSM = true
        · simp only [grayChargedStep, hphase, hslots, Bool.false_eq_true,
            ↓reduceIte, hgoal, deltaRound, current, localSM]
          split
          · split <;> simp
          · simp
        · simp [grayChargedStep, hphase, hslots, hgoal,
            deltaRound, current, localSM]

/-- From the `done` phase a further charged step stays in `done` and leaves the frozen rounds
unchanged. -/
lemma grayChargedStep_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedState n b) (m : FamilyServerMove)
    (hdone : st.phase = .done) :
    (grayChargedStep q L a e sigma A st m).phase = .done ∧
      (grayChargedStep q L a e sigma A st m).core.frozen =
        st.core.frozen := by
  simp [grayChargedStep, hdone]

/-- Once the controller is in the `done` phase at time `t`, it is in `done` with the same frozen
rounds at every later time. -/
lemma grayChargedStateAt_done_stable {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hdone : (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).phase = .done) :
    forall d,
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm (t + d)).phase = .done ∧
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm (t + d)).core.frozen =
        (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm t).core.frozen := by
  intro d
  induction d with
  | zero =>
      constructor
      · simpa
      · simp
  | succ d ih =>
      rw [Nat.add_succ, grayChargedStateAt_succ]
      have hstep := grayChargedStep_done q L a e sigma A
        (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm (t + d)) (sm (t + d)) ih.1
      exact ⟨hstep.1, hstep.2.trans ih.2⟩

/-- Under a legal server play, the codewords allocated locally to a list of slots at time `t` are
still allocated at any later time `U`. -/
lemma grayTailLocalAllocatedList_mono
    {n b D t U : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) (htU : t <= U)
    (slots : List (GrayTailSlot n b)) :
    allocationSubset
      (grayTailLocalAllocatedList
        (grayTailLocalServerMove D slots (sm t)))
      (grayTailLocalAllocatedList
        (grayTailLocalServerMove D slots (sm U))) := by
  intro z hz
  simp only [grayTailLocalAllocatedList, List.mem_flatMap] at hz
  obtain ⟨j, hjRange, hzLocal⟩ := hz
  have hjSlots : j < slots.length := by
    have hj := List.mem_range.mp hjRange
    simpa [grayTailLocalServerMove, truncFamilyServerMove,
      inTreeFamilyServerMove, extractGrandchildFamilyMove] using hj
  rw [getFamilyAlloc_grayTailLocalServerMove
    slots (sm t) j hjSlots [] (by simp)] at hzLocal
  obtain ⟨hzRaw, hzLength⟩ := mem_truncAlloc.mp hzLocal
  let slot : GrayTailSlot n b := slots.get ⟨j, hjSlots⟩
  have hzFamily :
      z ∈ getFamilyAlloc (sm t) slot.1.val
        [slot.2.1.val, slot.2.2.val] := by
    simpa [slot, getFamilyAlloc, getAlloc_extractSubtreeServerMove]
      using hzRaw
  have hmono := allocationSubset_mono_time
    (hsm.1 slot.1.val slot.1.isLt) htU
      [slot.2.1.val, slot.2.2.val]
  obtain ⟨w, hwFamily, hwz⟩ := hmono z hzFamily
  have hwRaw :
      w ∈ getAlloc
        (extractSubtreeServerMove slot.2.2.val
          (extractSubtreeServerMove slot.2.1.val
            (familyServerMoveAt (sm U) slot.1.val))) [] := by
    simpa [slot, getFamilyAlloc, getAlloc_extractSubtreeServerMove]
      using hwFamily
  have hwLength : w.length <= D :=
    le_trans hwz.length_le hzLength
  have hwLocal :
      w ∈ getFamilyAlloc
        (grayTailLocalServerMove D slots (sm U)) j [] := by
    rw [getFamilyAlloc_grayTailLocalServerMove
      slots (sm U) j hjSlots [] (by simp)]
    exact mem_truncAlloc.mpr ⟨hwRaw, hwLength⟩
  refine ⟨w, ?_, hwz⟩
  simp only [grayTailLocalAllocatedList, List.mem_flatMap]
  refine ⟨j, ?_, hwLocal⟩
  apply List.mem_range.mpr
  simpa [grayTailLocalServerMove, truncFamilyServerMove,
    inTreeFamilyServerMove, extractGrandchildFamilyMove] using hjSlots

/-- Freezing the current round changes nothing in the displayed family move. -/
lemma grayChargedTailFamilyMove_freeze {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (frozen : GrayTailFrozen n b) (p : GrayTailRound n b) :
    grayChargedTailFamilyMove source threshold eps
        (frozen ++ [p]) [] [] =
      grayChargedTailFamilyMove source threshold eps
        frozen p.slots p.move := by
  simp [grayChargedTailFamilyMove, grayTailEntries,
    grayTailFrozenEntries, grayTailSlotEntries]

/-- The family client move a charged controller state displays: the requests of its frozen rounds
together with the current move of its phase, which is empty in the `done` phase. -/
def grayChargedDisplayedMove {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayChargedState n b) : FamilyClientMove :=
  let current := match st.phase with
    | .done => []
    | .advantage => if st.core.slots.isEmpty then []
      else grayTailCurrentMove q L e sigma st.core
    | .spend pass => if st.core.slots.isEmpty then []
      else grayChargedSpendMove q L a e pass sigma st.core
  grayChargedTailFamilyMove (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (dyadicScale e)
    st.core.frozen st.core.slots current

/-- The move the charged strategy plays at time `t` is the move displayed by its controller state
at time `t`. -/
lemma playClientFamily_grayChargedStrategy
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    playClientFamily A n (grayChargedStrategy q L a e sigma) sm t =
      grayChargedDisplayedMove q L a e sigma
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t) := by
  dsimp [grayChargedDisplayedMove]
  cases t with
  | zero =>
      rw [playClientFamily]
      rfl
  | succ t =>
      rw [playClientFamily]
      rfl

/-- A controller in the `done` phase has no active slots left. -/
lemma grayChargedStateAt_slots_eq_nil_of_done
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat)
    (hdone : (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).phase = .done) :
    (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.slots = [] := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t = st at hcert hdone ⊢
  cases hcert with
  | advantage core hcore hsource hactive =>
      simp_all
  | spend pass core hspend =>
      simp_all
  | done core hdoneCert =>
      exact hdoneCert.slots_empty

/-- Once the controller is in the `done` phase at time `t`, the charged strategy keeps displaying
the move it displayed at `t`. -/
lemma playClientFamily_grayChargedStrategy_done_stable
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t d : Nat)
    (hdone : (grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .done) :
    playClientFamily A n (grayChargedStrategy q L a e sigma) sm (t + d) =
      playClientFamily A n (grayChargedStrategy q L a e sigma) sm t := by
  have hstable := grayChargedStateAt_done_stable
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t hdone d
  have hslotsT := grayChargedStateAt_slots_eq_nil_of_done
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t hdone
  have hslotsU := grayChargedStateAt_slots_eq_nil_of_done
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + d) hstable.1
  rw [playClientFamily_grayChargedStrategy,
    playClientFamily_grayChargedStrategy]
  simp [grayChargedDisplayedMove, hdone, hstable.1,
    hslotsT, hslotsU, hstable.2]

/-- One step after a final time the charged run is in the `done` phase. -/
lemma grayChargedFinalAt_successor_done
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    (grayChargedRunState q L a e n sigma A sm (T + 1)).phase = .done := by
  change (grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).phase = .done
  rw [grayChargedStateAt_succ]
  exact hfinal.2

/-- The frozen rounds at time `t` are a prefix of the frozen rounds at time `t + 1`. -/
lemma grayChargedStateAt_succ_frozen_prefix
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t).core.frozen <+:
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm (t + 1)).core.frozen := by
  rw [grayChargedStateAt_succ]
  exact grayChargedStep_frozen_prefix q L a e sigma A
    (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t) (sm t)

/-- Every round frozen by time `t` was closed against a server move of a time before `t`. -/
lemma grayChargedStateAt_frozen_serverTime_lt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat)
    (p : GrayTailRound n b)
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen) :
    p.serverTime < t := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t = st at hcert hp
  cases hcert with
  | advantage core hcore hsource hactive =>
      exact ((hcore.toCore (a := a) hsource).round_valid p hp).2.1
  | spend pass core hspend =>
      exact (hspend.core.round_valid p hp).2.1
  | done core hdone =>
      exact (hdone.core.round_valid p hp).2.1

/-- The codewords a frozen round recorded as allocated are still allocated by every later legal
server move. -/
lemma grayChargedStateAt_frozen_alloc_subset_late
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n b A sm)
    (t U : Nat) (htU : t <= U) (p : GrayTailRound n b)
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen) :
    allocationSubset p.allocated
      (grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm U))) := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  have hvalid :
      p.serverTime < t ∧
      p.allocated =
        grayTailLocalAllocatedList
          (grayTailLocalServerMove (p.epsDepth + L) p.slots
            (sm p.serverTime)) := by
    generalize hst :
      grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t = st at hcert hp
    cases hcert with
    | advantage core hcore hsource hactive =>
        exact ⟨((hcore.toCore (a := a) hsource).round_valid p hp).2.1,
          ((hcore.toCore (a := a) hsource).round_valid p hp).2.2.1⟩
    | spend pass core hspend =>
        exact ⟨(hspend.core.round_valid p hp).2.1,
          (hspend.core.round_valid p hp).2.2.1⟩
    | done core hdone =>
        exact ⟨(hdone.core.round_valid p hp).2.1,
          (hdone.core.round_valid p hp).2.2.1⟩
  rw [hvalid.2]
  exact grayTailLocalAllocatedList_mono hsm
    (le_trans (Nat.le_of_lt hvalid.1) htU) p.slots

/-- A tail step that finishes the tail displays the same family move as the state before it. -/
lemma grayChargedTailStep_done_display_eq
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = true) :
    grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayChargedTailStep q L a e sigma A st m).frozen [] [] =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        st.frozen st.slots
        (if st.slots.isEmpty then [] else grayTailCurrentMove q L e sigma st) := by
  rw [grayChargedTailStep_eq]
  rw [grayChargedTailStep_eq] at hdone
  by_cases hslots : st.slots.isEmpty = true
  · have hnil : st.slots = [] := List.isEmpty_iff.mp hslots
    simp [hactive, hnil]
  · by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · simp [hactive, hslots, hgoal, grayChargedTailFamilyMove_freeze]
    · simp [hactive, hslots, hgoal] at hdone

/-- A certified charged step that enters the `done` phase displays the same family move as the
state before it. -/
lemma grayChargedStep_done_display_eq
    {n b t : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayChargedState n b)
    (hcert : GrayChargedCertified q L a e sigma A sm t st)
    (hdone : (grayChargedStep q L a e sigma A st (sm t)).phase = .done) :
    grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A st (sm t)) =
      grayChargedDisplayedMove q L a e sigma st := by
  cases hcert with
  | done core hdoneCert =>
      simp [grayChargedDisplayedMove, grayChargedStep]
  | advantage core hcore hsource hactive =>
      let next := grayChargedTailStep q L a e sigma A core (sm t)
      by_cases hnext : next.done = true
      · have htail := grayChargedTailStep_done_display_eq
          q L a e sigma A core (sm t) hactive (by simpa [next] using hnext)
        have hstart :
            (grayChargedStartSpend q L a e A next (sm t)).phase = .done := by
          simpa [grayChargedStep, next, hnext] using hdone
        by_cases hslots :
            (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty = true
        · simpa [grayChargedStep, next, hnext, grayChargedStartSpend,
            hslots, grayChargedDisplayedMove] using htail
        · simp [grayChargedStartSpend, hslots] at hstart
      · simp [grayChargedStep, next, hnext] at hdone
  | spend pass core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      let r := core.frozen.length
      let epsRound := grayChargedSpendEps a L e pass
      let deltaRound := grayChargedSpendDelta a L e pass
      let current := grayChargedSpendMove q L a e pass sigma core
      let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
      by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
          core.slots.length core.unavailable current localSM = true
      · let allocated := grayTailLocalAllocatedList localSM
        let p : GrayTailRound n b :=
          { serverTime := core.time
            roundIndex := r
            epsDepth := epsRound
            slots := core.slots
            move := current
            allocated := allocated
            unavailable := core.unavailable }
        let frozen' := core.frozen ++ [p]
        have hfreeze := grayChargedTailFamilyMove_freeze
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) core.frozen p
        by_cases hpass : pass + 1 < 8
        · by_cases hnext :
              (grayChargedSlotsForPass q a e (pass + 1) frozen').isEmpty = true
          · simpa [grayChargedStep, hslots, hgoal, r, epsRound, deltaRound,
              current, localSM, allocated, p, frozen', hpass, hnext,
              grayChargedDisplayedMove] using hfreeze
          · simp [grayChargedStep, hslots, hgoal, r, epsRound, deltaRound,
              current, localSM, allocated, p, frozen', hpass, hnext] at hdone
        · simpa [grayChargedStep, hslots, hgoal, r, epsRound, deltaRound,
            current, localSM, allocated, p, frozen', hpass,
            grayChargedDisplayedMove] using hfreeze
      · simp [grayChargedStep, hslots, hgoal, deltaRound,
          current, localSM] at hdone

/-- One step after a final time the charged run displays the move it displayed at that time. -/
lemma grayChargedFinalAt_successor_move_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    grayChargedRunMove q L a e n sigma A sm (T + 1) =
      grayChargedRunMove q L a e n sigma A sm T := by
  change playClientFamily A n (grayChargedStrategy q L a e sigma) sm (T + 1) =
    playClientFamily A n (grayChargedStrategy q L a e sigma) sm T
  rw [playClientFamily_grayChargedStrategy,
    playClientFamily_grayChargedStrategy]
  rw [grayChargedStateAt_succ]
  exact grayChargedStep_done_display_eq q L a e sigma A sm
    (grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T)
    (grayChargedCertified_stateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T) hfinal.2

/-- After a final time `T` the charged run is in the `done` phase at every time `U ≥ T + 1`, with
the frozen rounds it had at `T + 1`. -/
lemma grayChargedFinalAt_done_stable
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    forall U, T + 1 <= U ->
      (grayChargedRunState q L a e n sigma A sm U).phase = .done ∧
        (grayChargedRunState q L a e n sigma A sm U).core.frozen =
          (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen := by
  intro U hU
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hU
  simpa [Nat.add_assoc] using
    (grayChargedStateAt_done_stable
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)
      (grayChargedFinalAt_successor_done hfinal) d)

/-- After a final time `T` the charged run displays, at every later time, the move it displayed
at `T`. -/
lemma grayChargedFinalAt_move_stable
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    forall U, T + 1 <= U ->
      grayChargedRunMove q L a e n sigma A sm U =
        grayChargedRunMove q L a e n sigma A sm T := by
  intro U hU
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hU
  calc
    grayChargedRunMove q L a e n sigma A sm (T + 1 + d) =
        grayChargedRunMove q L a e n sigma A sm (T + 1) := by
      exact playClientFamily_grayChargedStrategy_done_stable
        q L a e n sigma A sm (T + 1) d
          (grayChargedFinalAt_successor_done hfinal)
    _ = grayChargedRunMove q L a e n sigma A sm T :=
      grayChargedFinalAt_successor_move_eq hfinal

/-- A run with a final time `T` leaves the `advantage` phase at some time `t ≤ T`. -/
lemma grayChargedFinalAt_advantage_exit
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    exists t, t <= T ∧
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage ∧
      (grayChargedRunState q L a e n sigma A sm (t + 1)).phase ≠
        .advantage := by
  let P : Nat -> Prop := fun u =>
    (grayChargedRunState q L a e n sigma A sm u).phase ≠ .advantage
  have hP : exists u, P u := by
    refine ⟨T + 1, ?_⟩
    simp only [P]
    rw [grayChargedFinalAt_successor_done hfinal]
    simp
  let d := Nat.find hP
  have hdP : P d := Nat.find_spec hP
  have hzero :
      (grayChargedRunState q L a e n sigma A sm 0).phase = .advantage := by
    simp [grayChargedRunState, grayChargedStateAt, grayChargedFold,
      grayTailServerPrefix, grayChargedInitialState]
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0] at hdP
    exact hdP hzero
  let t := d - 1
  have htd : t + 1 = d := by
    dsimp [t]
    omega
  have htBefore :
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage := by
    by_contra ht
    have htP : P t := ht
    have hmin : d <= t := Nat.find_min' hP htP
    dsimp [t] at hmin
    omega
  have hdBound : d <= T + 1 := by
    apply Nat.find_min' hP
    simp only [P]
    rw [grayChargedFinalAt_successor_done hfinal]
    simp
  refine ⟨t, ?_, htBefore, ?_⟩
  · dsimp [t]
    omega
  · rw [htd]
    exact hdP

/-- At the time the run leaves the `advantage` phase, the underlying tail step reports the tail
as finished. -/
lemma grayCharged_advantage_exit_terminal_done
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage)
    (hafter :
      (grayChargedRunState q L a e n sigma A sm (t + 1)).phase ≠
        .advantage) :
    (grayChargedTailStep q L a e sigma A
      (grayChargedRunState q L a e n sigma A sm t).core
      (sm t)).done = true := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hstate :
    grayChargedRunState q L a e n sigma A sm t = st at hcert
  change grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hstate
  change (grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).phase = .advantage at hbefore
  rw [hstate] at hcert hbefore
  cases hcert with
  | advantage core hcore hsource hactive =>
      let next := grayChargedTailStep q L a e sigma A core (sm t)
      by_cases hnext : next.done = true
      · simpa [next] using hnext
      · apply (hafter ?_).elim
        change (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + 1)).phase = .advantage
        rw [grayChargedStateAt_succ, hstate]
        simp [grayChargedStep, next, hnext]
  | spend pass core hspend =>
      simp at hbefore
  | done core hdone =>
      simp at hbefore

/-- Finite rank of the syntactic controller phases.  Accepted recursive calls
strictly lower this rank; rejected local calls remain in the same spend pass. -/
def grayChargedPhaseRank : GrayChargedPhase -> Nat
  | .advantage => 5
  | .spend pass => 8 - pass
  | .done => 0

/-- The recursive server seen during every reachable spend round is legal. -/
def GrayChargedSpendFutureLegal
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  forall t pass,
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
    st.phase = .spend pass ->
      familyServerPlayLegal st.core.slots.length (grayTailBranch q L a e)
        st.core.unavailable
        (grayChargedSpendFutureServer a L e pass st.core sm)

/-- One reachable spend pass cannot wait forever: either it exposes an outer
positive unserved request or eventually leaves the current pass. -/
def GrayChargedSpendProgress
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  forall t pass,
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
    st.phase = .spend pass ->
      GrayChargedPositive q L a e n sigma A sm ∨
        exists u, t <= u ∧
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (u + 1)).phase ≠ .spend pass

/-- The geometric part of the final charge, separated from all numerical
accounting. -/
structure GrayChargedChargeGeometry
    (kappa beta : Rat) (epsDepth deltaDepth n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove) : Type where
  charge : FamilyGrayCharge
  sublist : charge ∈ (familyGrayChargeUniverse n deltaDepth).sublists
  cells_nodup : (charge.map Prod.snd).Nodup
  cells_valid : forall z, z ∈ charge ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList epsDepth deltaDepth
        (getFamilyAlloc s z.1 []) A
  aggregate_beta : (n : Rat) * beta <= grayChargeMass deltaDepth charge
  aggregate_request :
    kappa * totalRootRequest n c <= grayChargeMass deltaDepth charge

/-- The non-winning fields of the outer weak game specification. -/
structure GrayChargedOuterFields
    (q L B a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation) : Prop where
  legal : forall sm, familyServerPlayLegal n (grayTailBranch q L a e) A sm ->
    familyClientPlayLegal n (grayTailBranch q L a e) (dyadicScale a)
      (playClientFamily A n (grayChargedStrategy q L a e sigma) sm)
  minimum_request : forall sm,
    familyServerPlayLegal n (grayTailBranch q L a e) A sm -> forall t,
      familyRequestAvoidsSmall n
        ((1 / 2 : Rat) ^ (e + grayTailNewLoss q L))
        (playClientFamily A n (grayChargedStrategy q L a e sigma) sm t)
  range_supported : FamilyRangeSupported n (grayTailBranch q L a e) A
    (grayChargedStrategy q L a e sigma)
  tree_supported : FamilyTreeSupported n (2 * (q + 1)) A
    (grayChargedStrategy q L a e sigma)

end Kolmogorov
