import KolmogorovMathlib.MonotoneComplexity.GacsDayV2FieldsAssembly
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Coherence.Graft
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Coherence

/-!
# The monotonicity field of the V2 charged outer strategy

Port of `grayCharged_output_monotone` (`GacsDayChargedMonotonicity`) to
the V2 block controller: the outer move displayed by `grayChargedStrategyV2`
is, at every node of every root, non-decreasing in time — the second
conjunct of `familyClientPlayLegal`.  Together with the coherence half
(`grayChargedV2_output_coherentCap`, `GacsDayV2OuterCoherence`) this closes
the named obligation `GrayChargedLegalV2` (`GacsDayV2OuterFieldsAssembly`).

The displayed move is the two-level graft of the projected ledger entries,
and the graft is monotone in its entries (son bases and planted moves).
Along the certified run one step either

* keeps the frozen ledger and the active slots and replaces the current
  sub-move by its next exchange, which dominates it by the child rung's
  `legal` field against the legal local future server (advantage rounds:
  `grayChargedBlockRound_gameSpecV2`; spend passes:
  `grayChargedSpendRound_gameSpecV2`), transported through the replay
  identifications `grayBlockCurrentMoveV2_eq_futurePlay` /
  `grayBlockSpendMoveV2_eq_futurePlay`;
* freezes the current sub-move into the ledger (the frozen round stores the
  displayed slots and move verbatim) and starts a fresh block of slots whose
  entries are nonnegative by the coherence of the displayed current move at
  the next time (`grayChargedRunStateV2_displayedCurrent_coherent`) — this
  covers the freeze inside the advantage phase, the advantage→spend
  transition, the pass→pass transitions and every transition into `done`;
* or starts from the raised-service wait (v15.1 A3: the advantage phase over
  a done core, displaying the terminal ledger only — the never-run wide block
  of the done core is not displayed): the wait tick and the exit into `done`
  keep the display, the exit into the first spend pass adds its nonnegative
  entries;
* or is an idle/done tick, which leaves the display unchanged.
-/

namespace Kolmogorov

/-! ### Monotonicity of the graft in its entries -/

/-- The two-level graft is monotone in its entries: larger son bases and
larger planted moves give larger requests at every node of every root. -/
lemma getFamilyReq_grayChargedTailFamilyMove_mono {n b i : ℕ} {source : ℕ}
    {threshold eps : ℚ} (htheps : threshold ≤ eps) (hi : i < n) (x : GacsDayNode)
    {frozen1 frozen2 : GrayTailFrozen n b} {slots1 slots2 : List (GrayTailSlot n b)}
    {cur1 cur2 : FamilyClientMove}
    (hbase : ∀ c : Fin b,
      grayTailSonBase (grayTailEntries frozen1 slots1 cur1) ⟨i, hi⟩ c ≤
        grayTailSonBase (grayTailEntries frozen2 slots2 cur2) ⟨i, hi⟩ c)
    (hentry : ∀ (slot : GrayTailSlot n b) (y : GacsDayNode),
      getReq (grayTailEntryMove (grayTailEntries frozen1 slots1 cur1) slot) y ≤
        getReq (grayTailEntryMove (grayTailEntries frozen2 slots2 cur2) slot) y) :
    getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen1 slots1 cur1) i x ≤
      getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen2 slots2 cur2) i x := by
  change getReq
      (familyClientMoveAt (grayChargedTailFamilyMove source threshold eps frozen1 slots1 cur1) i)
        x ≤
    getReq
      (familyClientMoveAt (grayChargedTailFamilyMove source threshold eps frozen2 slots2 cur2) i)
        x
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hi, dif_pos hi]
  simp only [Option.getD_some]
  rcases x with _ | ⟨c, _ | ⟨c', y⟩⟩
  · rw [getReq_graftTwoLevel_root, getReq_graftTwoLevel_root]
    unfold grayChargedRootRequest
    exact Finset.sum_le_sum fun c _ => grayChargedSonRequest_mono htheps ⟨i, hi⟩ c (hbase c)
  · by_cases hc : c < b
    · rw [getReq_graftTwoLevel_son hc, getReq_graftTwoLevel_son hc]
      simp only [dif_pos hc]
      exact grayChargedSonRequest_mono htheps ⟨i, hi⟩ ⟨c, hc⟩ (hbase ⟨c, hc⟩)
    · have hc' : b ≤ c := Nat.le_of_not_gt hc
      rw [getReq_graftTwoLevel_of_ge hc', getReq_graftTwoLevel_of_ge hc']
  · by_cases hc : c < b
    · by_cases hc' : c' < b
      · rw [getReq_graftTwoLevel_grandson hc hc', getReq_graftTwoLevel_grandson hc hc']
        simp only [dif_pos hc, dif_pos hc']
        exact hentry (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) y
      · have hc'' : b ≤ c' := Nat.le_of_not_gt hc'
        rw [getReq_graftTwoLevel_of_son_ge hc hc'', getReq_graftTwoLevel_of_son_ge hc hc'']
    · have hc'' : b ≤ c := Nat.le_of_not_gt hc
      rw [getReq_graftTwoLevel_of_ge hc'', getReq_graftTwoLevel_of_ge hc'']

/-- Appending nonnegative entries only raises the graft. -/
lemma getFamilyReq_grayChargedTailFamilyMove_mono_append {n b i : ℕ} {source : ℕ}
    {threshold eps : ℚ} (htheps : threshold ≤ eps) (hi : i < n) (x : GacsDayNode)
    {frozen1 frozen2 : GrayTailFrozen n b} {slots1 slots2 : List (GrayTailSlot n b)}
    {cur1 cur2 : FamilyClientMove} {newEntries : List (GrayTailSlot n b × ClientMove)}
    (hentries : grayTailEntries frozen2 slots2 cur2 =
      grayTailEntries frozen1 slots1 cur1 ++ newEntries)
    (hnonneg : ∀ pr ∈ newEntries, ∀ y, 0 ≤ getReq pr.2 y) :
    getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen1 slots1 cur1) i x ≤
      getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen2 slots2 cur2) i x := by
  apply getFamilyReq_grayChargedTailFamilyMove_mono htheps hi x
  · intro c
    rw [hentries, grayTailSonBase_append_globalEntries]
    exact le_add_of_nonneg_right
      (grayTailSonBase_nonneg_global (entries := newEntries) (i := ⟨i, hi⟩) (c := c)
        (fun pr hpr => hnonneg pr hpr []))
  · intro slot y
    rw [hentries]
    exact grayTailEntryMove_mono_append _ _ hnonneg slot y

/-- Raising the current sub-move at every active slot raises the graft. -/
lemma getFamilyReq_grayChargedTailFamilyMove_mono_current {n b i : ℕ} {source : ℕ}
    {threshold eps : ℚ} (htheps : threshold ≤ eps) (hi : i < n) (x : GacsDayNode)
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {move1 move2 : FamilyClientMove}
    (hmove : ∀ j < slots.length, ∀ y,
      getReq (familyClientMoveAt move1 j) y ≤ getReq (familyClientMoveAt move2 j) y) :
    getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen slots move1) i x ≤
      getFamilyReq (grayChargedTailFamilyMove source threshold eps frozen slots move2) i x := by
  apply getFamilyReq_grayChargedTailFamilyMove_mono htheps hi x
  · intro c
    unfold grayTailEntries
    rw [grayTailSonBase_append_globalEntries, grayTailSonBase_append_globalEntries]
    exact add_le_add le_rfl
      (grayTailSonBase_slotEntries_mono slots move1 move2 (fun j hj => hmove j hj []) ⟨i, hi⟩ c)
  · intro slot y
    exact grayTailEntryMove_mono_append_of_frozen frozen slots move1 move2 hmove slot y

/-! ### One step of the displayed move, abstractly -/

/-- A step between active cores keeping the ledger and the active slots is
monotone as soon as the current sub-move is. -/
lemma grayChargedDisplayedMoveV2_mono_of_same {n b q L a e i : ℕ}
    {sigma : FamilyStrategyScheme} (hi : i < n) (x : GacsDayNode)
    {st st' : GrayChargedStateV2 n b}
    (hfrozen : st'.core.frozen = st.core.frozen) (hslots : st'.core.slots = st.core.slots)
    (hdone : st.core.done = false) (hdone' : st'.core.done = false)
    (hmove : ∀ j < st.core.slots.length, ∀ y,
      getReq (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st) j) y ≤
        getReq (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st') j) y) :
    getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st') i x := by
  rw [grayChargedDisplayedMoveV2_eq_current, grayChargedDisplayedMoveV2_eq_current, hfrozen,
    hslots, hdone, hdone']
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact getFamilyReq_grayChargedTailFamilyMove_mono_current (grayChargedThreshold_le_eps q e)
    hi x hmove

/-- A freeze step from an active core — the displayed slots and current
sub-move are stored in a new frozen round, and a fresh (possibly empty, and
not displayed on a done core) block of slots with a nonnegative current
sub-move is displayed — is monotone. -/
lemma grayChargedDisplayedMoveV2_mono_of_freeze {n b q L a e i : ℕ}
    {sigma : FamilyStrategyScheme} (hi : i < n) (x : GacsDayNode)
    {st st' : GrayChargedStateV2 n b} (hdone : st.core.done = false)
    (p : GrayTailRoundV2 n b)
    (hfrozen : st'.core.frozen = st.core.frozen ++ [p])
    (hslots : p.slots = st.core.slots)
    (hmove : p.move = grayChargedCurrentMoveV2 q L a e sigma st)
    (hnonneg : ∀ j < st'.core.slots.length, ∀ y,
      0 ≤ getReq (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st') j) y) :
    getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st') i x := by
  rw [grayChargedDisplayedMoveV2_eq_current, grayChargedDisplayedMoveV2_eq_current, hdone]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hentries : grayTailEntries (st'.core.frozen.map GrayTailRoundV2.toV1)
      (if st'.core.done then [] else st'.core.slots)
      (grayChargedCurrentMoveV2 q L a e sigma st') =
    grayTailEntries (st.core.frozen.map GrayTailRoundV2.toV1) st.core.slots
      (grayChargedCurrentMoveV2 q L a e sigma st) ++
      grayTailSlotEntries (if st'.core.done then [] else st'.core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma st') := by
    rw [hfrozen, List.map_append, List.map_cons, List.map_nil]
    unfold grayTailEntries
    rw [grayTailFrozenEntries_append_one]
    have h1 : p.toV1.slots = st.core.slots := hslots
    have h2 : p.toV1.move = grayChargedCurrentMoveV2 q L a e sigma st := hmove
    rw [h1, h2]
  refine getFamilyReq_grayChargedTailFamilyMove_mono_append (grayChargedThreshold_le_eps q e)
    hi x hentries (fun pr hpr y => getReq_slotEntries_mem_nonneg _ _ ?_ pr hpr y)
  intro j hj y
  by_cases hd : st'.core.done = true
  · rw [if_pos hd] at hj
    simp at hj
  · rw [if_neg hd] at hj
    exact hnonneg j hj y

/-- From a wait state — the advantage phase over a done core, displaying the
terminal ledger only — any state keeping the frozen ledger and displaying a
nonnegative current sub-move dominates the display: the wait tick, the exit
into `done` and the exit into the first spend pass. -/
lemma grayChargedDisplayedMoveV2_mono_of_wait {n b q L a e i : ℕ}
    {sigma : FamilyStrategyScheme} (hi : i < n) (x : GacsDayNode)
    {st st' : GrayChargedStateV2 n b}
    (hphase : st.phase = .advantage) (hdone : st.core.done = true)
    (hfrozen : st'.core.frozen = st.core.frozen)
    (hnonneg : ∀ j < st'.core.slots.length, ∀ y,
      0 ≤ getReq (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st') j) y) :
    getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma st') i x := by
  have hcur : grayChargedCurrentMoveV2 q L a e sigma st = [] := by
    simp [grayChargedCurrentMoveV2, hphase, hdone]
  rw [grayChargedDisplayedMoveV2_eq_current, grayChargedDisplayedMoveV2_eq_current, hfrozen,
    hcur, if_pos hdone]
  have hentries : grayTailEntries (st.core.frozen.map GrayTailRoundV2.toV1)
      (if st'.core.done then [] else st'.core.slots)
      (grayChargedCurrentMoveV2 q L a e sigma st') =
    grayTailEntries (st.core.frozen.map GrayTailRoundV2.toV1) [] [] ++
      grayTailSlotEntries (if st'.core.done then [] else st'.core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma st') := by
    simp only [grayTailEntries, grayTailSlotEntries, List.length_nil, List.ofFn_zero,
      List.append_nil]
  refine getFamilyReq_grayChargedTailFamilyMove_mono_append (grayChargedThreshold_le_eps q e)
    hi x hentries (fun pr hpr y => getReq_slotEntries_mem_nonneg _ _ ?_ pr hpr y)
  intro j hj y
  by_cases hd : st'.core.done = true
  · rw [if_pos hd] at hj
    simp at hj
  · rw [if_neg hd] at hj
    exact hnonneg j hj y

/-! ### The current sub-moves are monotone in the exchange -/

/-- One rejected exchange of an active V2 advantage round raises the current
sub-move at every active slot: the pinned rung's `legal` for the block round
strategy against the legal V2 future server, transported through the replay
identification. -/
lemma grayBlockCurrentMoveV2_mono_of_legal
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hhist : GrayBlockHistoryOKV2 q L e sigma st)
    (htrace : GrayTailTraceV2 q L e sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayBlockFutureServerV2 q L e st sm))
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    let current := grayBlockCurrentMoveV2 q L e sigma st
    let localSM := grayTailLocalServerMove
      (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)
    let st' : GrayTailStateV2 n (grayTailBranch q L a e) :=
      { st with
        time := st.time + 1
        history := (st.history.1 ++ [current], st.history.2 ++ [localSM]) }
    GrayBlockHistoryOKV2 q L e sigma st' → GrayTailTraceV2 q L e sm (t + 1) st' →
    ∀ j < st.slots.length, ∀ y,
      getReq (familyClientMoveAt current j) y ≤
        getReq (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma st') j) y := by
  dsimp only
  intro hhist' htrace' j hj y
  have hspec := (grayChargedBlockRound_gameSpecV2 ha hae hL hRung hactive).weak
  have hlegal := hspec.legal (grayBlockFutureServerV2 q L e st sm) hlocal
  have hcurr := grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist htrace
  have hcurr' := grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist' htrace'
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr']
  simpa [grayBlockFutureServerV2, grayBlockRoundStrategyV2] using
    hlegal.2 st.history.2.length j hj y

/-- One rejected exchange of a V2 spend pass raises the current sub-move at
every active slot (the pinned rung's `legal` at the pass anchor). -/
lemma grayBlockSpendMoveV2_mono_of_legal
    {q L a e n t pass : ℕ} {sigma : FamilyStrategyScheme} {sm : ℕ → FamilyServerMove}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayChargedSpendFutureServerV2 a L e pass st sm))
    (hslots : st.slots.isEmpty = false) :
    let current := grayBlockSpendMoveV2 q L a e pass sigma st
    let localSM := grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots (sm t)
    let st' : GrayTailStateV2 n (grayTailBranch q L a e) :=
      { st with
        time := st.time + 1
        history := (st.history.1 ++ [current], st.history.2 ++ [localSM]) }
    ∀ j < st.slots.length, ∀ y,
      getReq (familyClientMoveAt current j) y ≤
        getReq (familyClientMoveAt (grayBlockSpendMoveV2 q L a e pass sigma st') j) y := by
  dsimp only
  intro j hj y
  have hspec :=
    (grayChargedSpendRound_gameSpecV2 (st := st) (pass := pass) hL hRung hslots).weak
  have hlegal := hspec.legal (grayChargedSpendFutureServerV2 a L e pass st sm) hlocal
  have hst' := grayChargedSpendReplayOKV2_append hst rfl
  have hcurr := grayBlockSpendMoveV2_eq_futurePlay hst
  have hcurr' := grayBlockSpendMoveV2_eq_futurePlay hst'
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr']
  simpa [grayChargedSpendFutureServerV2] using hlegal.2 st.history.2.length j hj y

/-! ### The continuing steps -/

/-- A rejected exchange in the advantage phase (nonempty slots) raises the
displayed move. -/
lemma grayChargedDisplayedMoveV2_step_mono_advantage_continue
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (core : GrayTailStateV2 n (grayTailBranch q L a e))
    (hcore : GrayChargedBlockTailCertifiedV2 q L e A sm t core)
    (hhist : GrayBlockHistoryOKV2 q L e sigma core)
    (htrace : GrayTailTraceV2 q L e sm t core)
    (hactive : core.done = false) (hslots : core.slots.isEmpty = false)
    (hgoal : grayChargedBlockGoalAtB q L e core.frozen.length core.slots.length
      core.unavailable (grayBlockCurrentMoveV2 q L e sigma core)
      (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
        core.slots (sm t)) = false)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma
        { phase := .advantage, core := core }) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma
        (grayChargedStepV2 q L a e sigma A { phase := .advantage, core := core } (sm t))) i x := by
  have hact : (core.done || core.slots.isEmpty) ≠ true := by simp [hactive, hslots]
  have hstepCore : grayChargedBlockTailStepV2 q L a e sigma A core (sm t) =
      { core with
        time := core.time + 1
        history := (core.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma core],
          core.history.2 ++ [grayTailLocalServerMove
            (grayTailRoundDelta q L e core.frozen.length) core.slots (sm t)]) } := by
    simp [grayChargedBlockTailStepV2, hactive, hslots, hgoal]
  have hhist' := grayChargedBlockHistoryOKV2_step q L a e sigma A core (sm t) hhist
  have htrace' := grayChargedBlockTailTraceV2_step (a := a) (A := A) sigma htrace
  rw [hstepCore] at hhist' htrace'
  have hlocal := grayChargedBlockTailFutureServerV2_legal hcore hsm
  have hmove := grayBlockCurrentMoveV2_mono_of_legal ha hae hL hRung core hhist htrace hlocal
    hact hhist' htrace'
  have hnext : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = false := by
    rw [hstepCore]
    exact hactive
  have hphase : ({ phase := .advantage, core := core } :
      GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
  rw [grayChargedStepV2_advantage_continue q L a e sigma A { phase := .advantage, core := core }
    (sm t) hphase hnext, hstepCore]
  refine grayChargedDisplayedMoveV2_mono_of_same hi x rfl rfl hactive hactive ?_
  intro j hj y
  simpa [grayChargedCurrentMoveV2, hactive, hslots] using hmove j hj y

/-- A rejected exchange in a spend pass raises the displayed move. -/
lemma grayChargedDisplayedMoveV2_step_mono_spend_continue
    {q L a e n t pass : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (core : GrayTailStateV2 n (grayTailBranch q L a e))
    (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass core)
    (hok : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t core)
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length core.unavailable
      (grayBlockSpendMoveV2 q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) = false)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma
        { phase := .spend pass, core := core }) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q L a e sigma
        (grayChargedStepV2 q L a e sigma A { phase := .spend pass, core := core } (sm t))) i x := by
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  have hstep : grayChargedStepV2 q L a e sigma A { phase := .spend pass, core := core } (sm t) =
      { phase := .spend pass
        core := { core with
          time := core.time + 1
          history := (core.history.1 ++ [grayBlockSpendMoveV2 q L a e pass sigma core],
            core.history.2 ++ [grayTailLocalServerMove
              (grayChargedSpendDelta a L e pass) core.slots (sm t)]) } } := by
    simp [grayChargedStepV2, hslots, hgoal]
  have hlocal := grayChargedSpendFutureServerV2_legal hspend hsm
  have hmove := grayBlockSpendMoveV2_mono_of_legal hL hRung core hok hlocal hslots
  rw [hstep]
  refine grayChargedDisplayedMoveV2_mono_of_same hi x rfl rfl hspend.done_false
    hspend.done_false ?_
  intro j hj y
  simpa [grayChargedCurrentMoveV2, hslots] using hmove j hj y

/-! ### The run -/

/-- **The displayed V2 move is non-decreasing across every step of the
certified run**, at the pinned gap `L = grayFootprint q`,
`e = a + 8 * L + 3` (both written out in the statement). -/
theorem grayChargedDisplayedMoveV2_stateAt_succ_mono
    {q a n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm)
    (t i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMoveV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) sigma
        (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t)) i x ≤
      getFamilyReq (grayChargedDisplayedMoveV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) sigma
        (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm (t + 1))) i x := by
  obtain ⟨L, hL⟩ : ∃ L, L = grayFootprint q := ⟨grayFootprint q, rfl⟩
  rw [← hL] at hsm ⊢
  set e := a + 8 * L + 3 with hpin
  have hae : a ≤ e := by rw [hpin]; omega
  have hnonneg : ∀ j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.slots.length, ∀ y,
      0 ≤ getReq (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + 1))) j) y :=
    fun j hj y =>
      (grayChargedRunStateV2_displayedCurrent_coherent ha hae hL hRung hsm (t + 1) j hj).1 y
  rw [grayChargedRunStateV2_succ] at hnonneg ⊢
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  have hhistT := grayChargedBlockHistoryOKV2_stateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have htraceT := grayChargedBlockTailTraceV2_stateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have hcoreEq := grayChargedRunStateV2_core_eq_tailStateAt (n := n) q L a e sigma A sm t
  have hokT := grayChargedRunStateV2_spendReplayOK (n := n) q L a e sigma A sm t
  generalize grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert hnonneg hcoreEq hokT ⊢
  by_cases hdoneStep : (grayChargedStepV2 q L a e sigma A st (sm t)).phase = .done
  · have heq := grayChargedStepV2_done_display_eq q L a e sigma A sm st hcert hdoneStep
    exact (congrArg (fun m => getFamilyReq m i x) heq).symm.le
  cases hcert with
  | done core hdone =>
      exact absurd
        (grayChargedStepV2_done_frozen q L a e sigma A
          { phase := .done, core := core } (sm t) rfl).1
        hdoneStep
  | advantage core hcore _hsource hactive =>
      have hcoreEq' : core = grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t := hcoreEq rfl
      rw [← hcoreEq'] at hhistT htraceT
      by_cases hslots : core.slots.isEmpty = true
      · -- idle tick of an active core without slots: the display is unchanged
        have hstepCore : grayChargedBlockTailStepV2 q L a e sigma A core (sm t) =
            { core with time := core.time + 1 } := by
          simp [grayChargedBlockTailStepV2, hactive, hslots]
        have hnext : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = false := by
          rw [hstepCore]
          exact hactive
        have hphase : ({ phase := .advantage, core := core } :
            GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
        rw [grayChargedStepV2_advantage_continue q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase hnext, hstepCore]
        refine grayChargedDisplayedMoveV2_mono_of_same hi x rfl rfl hactive hactive ?_
        intro j _ y
        simp [grayChargedCurrentMoveV2, hslots]
      · have hslots' : core.slots.isEmpty = false := by simpa using hslots
        by_cases hgoal : grayChargedBlockGoalAtB q L e core.frozen.length core.slots.length
            core.unavailable (grayBlockCurrentMoveV2 q L e sigma core)
            (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
              core.slots (sm t)) = true
        · -- freeze: inside the advantage phase, into the first pass, or into `done`
          have hnf := grayChargedBlockTailStepV2_accept_frozen_eq q L a e sigma A core (sm t)
            hactive hslots' hgoal
          obtain ⟨p, hp, hpslots, hpmove⟩ : ∃ p : GrayTailRoundV2 n (grayTailBranch q L a e),
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).frozen =
                  core.frozen ++ [p] ∧
                p.slots = core.slots ∧ p.move = grayBlockCurrentMoveV2 q L e sigma core :=
            ⟨_, hnf, rfl, rfl⟩
          have hphase : ({ phase := .advantage, core := core } :
              GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
          have hfrozen : (grayChargedStepV2 q L a e sigma A
              { phase := .advantage, core := core } (sm t)).core.frozen =
                core.frozen ++ [p] := by
            by_cases hnd : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
            · by_cases hserved : grayChargedWaitServedB q a e
                  (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
              · rw [grayChargedStepV2_advantage_exit q L a e sigma A
                  { phase := .advantage, core := core } (sm t) hphase hnd hserved,
                  grayChargedStartSpendV2_frozen, hp]
              · have hserved' : grayChargedWaitServedB q a e
                    (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) =
                      false := by
                  simpa using hserved
                rw [grayChargedStepV2_advantage_wait q L a e sigma A
                  { phase := .advantage, core := core } (sm t) hphase hnd hserved']
                exact hp
            · have hnd' : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done =
                  false := by simpa using hnd
              rw [grayChargedStepV2_advantage_continue q L a e sigma A
                { phase := .advantage, core := core } (sm t) hphase hnd']
              exact hp
          refine grayChargedDisplayedMoveV2_mono_of_freeze
            (st := { phase := .advantage, core := core }) hi x hactive p hfrozen hpslots ?_
            hnonneg
          rw [hpmove]
          simp [grayChargedCurrentMoveV2, hactive, hslots']
        · have hgoal' : grayChargedBlockGoalAtB q L e core.frozen.length core.slots.length
              core.unavailable (grayBlockCurrentMoveV2 q L e sigma core)
              (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
                core.slots (sm t)) = false := by simpa using hgoal
          exact grayChargedDisplayedMoveV2_step_mono_advantage_continue ha hae hL hRung hsm
            core hcore hhistT htraceT hactive hslots' hgoal' i hi x
  | wait core _hcore _hsource hdone =>
      -- the raised-service wait: a tick keeps the terminal display, the exit keeps the
      -- ledger and displays the (nonnegative) first spend pass, if any
      have hphase : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      exact grayChargedDisplayedMoveV2_mono_of_wait hi x hphase hdone
        (grayChargedStepV2_frozen_of_wait q L a e sigma A core (sm t) hdone) hnonneg
  | spend pass core hspend =>
      have hok : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t core := hokT pass rfl
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length
          core.unavailable (grayBlockSpendMoveV2 q L a e pass sigma core)
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) = true
      · -- freeze: into the next pass or into `done`
        obtain ⟨p, hfrozen, hpslots, hpmove⟩ :
            ∃ p : GrayTailRoundV2 n (grayTailBranch q L a e),
              (grayChargedStepV2 q L a e sigma A { phase := .spend pass, core := core }
                (sm t)).core.frozen = core.frozen ++ [p] ∧
              p.slots = core.slots ∧ p.move = grayBlockSpendMoveV2 q L a e pass sigma core := by
          simp only [grayChargedStepV2, hslots, Bool.false_eq_true, ↓reduceIte, hgoal]
          split
          · split
            · exact ⟨_, rfl, rfl, rfl⟩
            · exact ⟨_, rfl, rfl, rfl⟩
          · exact ⟨_, rfl, rfl, rfl⟩
        refine grayChargedDisplayedMoveV2_mono_of_freeze
          (st := { phase := .spend pass, core := core }) hi x hspend.done_false p hfrozen
          hpslots ?_ hnonneg
        rw [hpmove]
        simp [grayChargedCurrentMoveV2, hslots]
      · have hgoal' : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length
            core.unavailable (grayBlockSpendMoveV2 q L a e pass sigma core)
            (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) =
              false := by simpa using hgoal
        exact grayChargedDisplayedMoveV2_step_mono_spend_continue hL hRung hsm core hspend hok
          hgoal' i hi x

/-- **The monotonicity field of the V2 charged outer strategy** at the pinned
gap `L = grayFootprint q`, `e = a + 8 * L + 3` (both written out in the
statement): at every node of every root, the displayed request is
non-decreasing in time. -/
theorem grayChargedV2_output_monotone
    {q a n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm)
    (i : ℕ) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (playClientFamily A n (grayChargedStrategyV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) sigma) sm t) i x ≤
      getFamilyReq (playClientFamily A n (grayChargedStrategyV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) sigma) sm (t + 1)) i x := by
  rw [playClientFamily_grayChargedStrategyV2, playClientFamily_grayChargedStrategyV2]
  exact grayChargedDisplayedMoveV2_stateAt_succ_mono ha hRung hsm t i hi x

/-- **The named obligation `GrayChargedLegalV2` is a theorem** at the pinned
gap `L = grayFootprint q`, `e = a + 8 * L + 3`, from the pinned child rung. -/
theorem grayChargedLegalV2_of_rung
    {q a n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hRung : PinnedChargedRung 4 q sigma) :
    GrayChargedLegalV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3) n sigma A :=
  fun _sm hsm =>
    ⟨fun t i hi => grayChargedV2_output_coherentCap (t := t) ha hRung hsm i hi,
      fun t i hi x => grayChargedV2_output_monotone (t := t) ha hRung hsm i hi x⟩

end Kolmogorov
