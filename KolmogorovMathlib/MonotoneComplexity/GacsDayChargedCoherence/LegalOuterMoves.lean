import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOuterSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTerminationSupport

/-!
# Legality of the moves the charged client makes

The charged client is defined by recursion, so its moves must be legal both for the recursive
call and for the outer play. `grayTailFutureServer_legal_outer` and
`grayChargedCoreFutureServer_legal_outer` show that the server play handed to a recursive call is
legal for the slots that call owns; `grayChargedCurrentMove_coherent_of_legal` and
`grayChargedSpendMove_coherent_of_legal` show that the advantage and spend moves are request
coherent along a certified history; and their run-level forms
`grayChargedCurrentMove_stateAt_coherent`, `grayChargedSpendMove_stateAt_coherent` transport this
to every state of a run against a legal server play. `requestCoherentCap.mono_cap` and
`grayChargedCallScale_le_spendAlpha` are the monotonicity facts used to move between caps.
-/



namespace Kolmogorov

/-- The server play seen by the recursive call inside a tail state is legal for the slots of that
state, provided the slots are distinct and the outer play is legal. -/
lemma grayTailFutureServer_legal_outer {n b : Nat}
    (q L e : Nat) {A : Allocation}
    {st : GrayTailState n b} (hnodup : st.slots.Nodup)
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b A
      (grayTailFutureServer q L e st sm) := by
  have hshift :
      familyServerPlayLegal n b A
        (fun t => sm (st.roundStart + t)) := by
    simpa [Nat.add_comm] using
      familyServerPlayLegal_shift hsm st.roundStart
  unfold grayTailFutureServer grayTailLocalServerMove
  exact familyServerPlayLegal_truncFamily
    (familyServerPlayLegal_inTreeFamily
      (serverPlayLegal_extractGrandchild st.slots hnodup
        hshift))

/-- For a certified core, the server play seen by the recursive call is legal for the slots of
the state against its unavailable set. -/
theorem grayChargedCoreFutureServer_legal_outer {n b q L e t : Nat}
    {A : Allocation} {st : GrayTailState n b}
    {sm : Nat -> FamilyServerMove}
    (hcore : GrayChargedTailCertified q L e A sm t st)
    (_hround : st.frozen.length < grayTailRoundCount q)
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayTailFutureServer q L e st sm) := by
  have hnodup_all := hcore.shape.allSlots_nodup
  obtain ⟨-, hnodup_slots, hdisjoint⟩ := List.nodup_append.mp hnodup_all
  have hA := grayTailFutureServer_legal_outer q L e hnodup_slots hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  rw [hcore.unavailable_snap]
  intro c hc a ha
  rcases List.mem_append.mp ha with haA | haH
  · exact hA.2.2 u i hi x c hc a haA
  · -- v14 §9.6: the two-case length-cap argument via the untouchable lemma.
    let newSlot : GrayTailSlot n b := st.slots.get ⟨i, hi⟩
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayTailFutureServer] using hc
    have hx : forall d, d ∈ x -> d < b := by
      by_contra hbad
      have hz := getFamilyAlloc_grayTailLocalServerMove_of_not_mem
        (eps := grayTailRoundDelta q L e st.frozen.length)
        st.slots (sm (st.roundStart + u)) i hi x hbad
      rw [hz] at hcLocal
      simp at hcLocal
    have hcFull : c ∈ getFamilyAlloc (sm (st.roundStart + u)) newSlot.1.val
        (grayTailSlotNode newSlot ++ x) := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      have hextract := (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).1
      simpa [grayTailSlotNode, getFamilyAlloc] using hextract
    have hcLength :
        c.length <= grayTailRoundDelta q L e st.frozen.length := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).2
    have hnewMem : newSlot ∈ st.slots := List.get_mem st.slots ⟨i, hi⟩
    have hx' : forall d, d ∈ grayTailSlotNode newSlot ++ x -> d < b := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_cons.mp hd with hd | hd
        · exact hd ▸ newSlot.2.1.isLt
        · have hde : d = newSlot.2.2.val := by simpa using hd
          exact hde ▸ newSlot.2.2.isLt
      · exact hx d hd
    cases hlast : st.frozen.getLast? with
    | none =>
        rw [hlast] at haH
        simp [grayHarvestSnapshot, grayHarvest_nil] at haH
    | some pLast =>
        rw [hlast] at haH
        simp only [Option.map_some, grayHarvestSnapshot] at haH
        exact grayHarvest_untouchable hsm hnewMem hx' hcFull hcLength haH

/-- Along a certified history and a legal localised play, the current advantage move is request
coherent with cap `dyadicScale (grayCallDepth q e)` in every slot. -/
lemma grayChargedCurrentMove_coherent_of_legal
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
    ∀ j < st.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayCallDepth q e))
        (familyClientMoveAt (grayTailCurrentMove q L e sigma st) j) := by
  have hcall : 1 <= grayCallDepth q e := by
    unfold grayCallDepth
    omega
  have heps :
      grayCallDepth q e <=
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
  have hlegal := hspec.legal
    (grayTailFutureServer q L e st sm) hlocal
  have hcurr := grayTailCurrentMove_eq_futurePlay
    q L e sigma hhist htrace
  intro j hj
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
  exact hlegal.1 st.history.2.length j hj

/-- Request coherence is preserved when the cap is enlarged. -/
lemma requestCoherentCap.mono_cap {b : Nat} {alpha alpha' : Rat}
    {req : ClientMove}
    (h : requestCoherentCap b alpha req) (hle : alpha <= alpha') :
    requestCoherentCap b alpha' req :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

/-- The call scale `dyadicScale (grayCallDepth q e)` is at most the spend scale
`dyadicScale (grayChargedSpendAlphaDepth a)` when `a ≤ e`. -/
lemma grayChargedCallScale_le_spendAlpha {q a e : Nat} (hae : a <= e) :
    dyadicScale (grayCallDepth q e) <=
      dyadicScale (grayChargedSpendAlphaDepth a) := by
  apply dyadicScale_antitone
  have h4 : 2 ^ 2 <= 3 * q + 5 := by omega
  have := Nat.lt_size.mpr h4
  unfold grayCallDepth grayChargedSpendAlphaDepth
  omega

/-- Along a certified spend history and a legal localised play, the spend move is request
coherent with cap `dyadicScale (grayChargedSpendAlphaDepth a)` in every slot. -/
lemma grayChargedSpendMove_coherent_of_legal
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
    ∀ j < st.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt
          (grayChargedSpendMove q L a e pass sigma st) j) := by
  have hspec := grayFamilyGameSpec_mono_branching
    (grayChargedSpendBranch_le pass hB)
    (hRung (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass)
      (by unfold grayChargedSpendAlphaDepth; omega)
      (le_max_left _ _) st.slots.length st.unavailable hne).weak
  have hlegal := hspec.legal
    (grayChargedSpendFutureServer a L e pass st sm) hlocal
  have hcurr := grayChargedSpendMove_eq_futurePlay
    q L a e pass sigma hhist htrace
  intro j hj
  rw [congrArg (fun m => familyClientMoveAt m j) hcurr]
  exact hlegal.1 st.history.2.length j hj

/-- In the `advantage` phase of a run against a legal server play, the current move is request
coherent with cap `dyadicScale (grayCallDepth q e)` in every slot. -/
lemma grayChargedCurrentMove_stateAt_coherent
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    st.phase = .advantage ->
      forall _hne : 1 <= st.core.slots.length,
        ∀ j < st.core.slots.length,
          requestCoherentCap (grayTailBranch q L a e)
            (dyadicScale (grayCallDepth q e))
            (familyClientMoveAt
              (grayTailCurrentMove q L e sigma st.core) j) := by
  dsimp only
  intro hadv hne
  have hhist := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have htrace := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hstEq :
      grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hhist htrace hcert hadv hne ⊢
  cases hcert with
  | advantage core htail hsource hdone =>
      have hroundAdv :
          core.frozen.length < grayChargedAdvantageRoundCount q :=
        htail.frozen_bound.2 hdone
      have hround : core.frozen.length < grayTailRoundCount q := by
        have hrc :
            grayTailRoundCount q = grayChargedAdvantageRoundCount q + 8 := by
          unfold grayTailRoundCount grayChargedAdvantageRoundCount
          rfl
        omega
      have hhist' : GrayTailHistoryOK q L e sigma core := by
        unfold GrayChargedHistoryOK at hhist
        simpa [grayChargedRoundStrategy] using hhist
      have htrace' : GrayTailTrace q L e sm t core := by
        have h := htrace
        unfold GrayChargedTrace at h
        simp only [grayChargedRoundDelta] at h
        exact GrayTailTraceAt.toTrace h
      exact grayChargedCurrentMove_coherent_of_legal
        ha hae hB hRung core hhist' htrace'
        (grayChargedCoreFutureServer_legal_outer htail hround hsm) hne
  | spend pass core hspend =>
      exact absurd hadv (by simp)
  | done core hdone =>
      exact absurd hadv (by simp)

/-- In a spend pass of a run against a legal server play, the spend move is request coherent with
cap `dyadicScale (grayChargedSpendAlphaDepth a)` in every slot. -/
lemma grayChargedSpendMove_stateAt_coherent
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    forall pass, st.phase = .spend pass ->
      1 <= st.core.slots.length ->
      ∀ j < st.core.slots.length,
        requestCoherentCap (grayTailBranch q L a e)
          (dyadicScale (grayChargedSpendAlphaDepth a))
          (familyClientMoveAt
            (grayChargedSpendMove q L a e pass sigma st.core) j) := by
  dsimp only
  intro pass hphase hne
  have hhist := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have htrace := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hstEq :
      grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hhist htrace hcert hphase hne ⊢
  cases hcert with
  | advantage core htail hsource hdone =>
      exact absurd hphase (by simp)
  | done core hdone =>
      exact absurd hphase (by simp)
  | spend pass2 core hspend =>
      have hpassEq : pass2 = pass := by
        have := hphase
        simp only at this
        cases this
        rfl
      cases hpassEq
      have hhist' : GrayChargedHistoryOK q L a e sigma
          (n := n) (b := grayTailBranch q L a e)
          { phase := .spend pass, core := core } := hhist
      have htrace' : GrayTailTraceAt
          (grayChargedSpendDelta a L e pass) sm t core := htrace
      have hlocal := grayChargedSpendFutureServer_legal
        hroom hspend.pass_lt hspend.core hspend.unavailable_snap hsm
      exact grayChargedSpendMove_coherent_of_legal
        hB hRung core hhist' htrace' hlocal hne

/-- Every move recorded in the frozen rounds is request coherent with cap
`dyadicScale (grayChargedSpendAlphaDepth a)` in each of its slots. -/
def GrayChargedFrozenCoherent {n b : Nat}
    (_q a _e : Nat) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
      (familyClientMoveAt p.move j)

/-- Freezing an advantage round preserves coherence of the frozen rounds. -/
lemma grayChargedFrozenCoherent_append
    {q L a e n b : Nat} {sigma : FamilyStrategyScheme}
    {m : FamilyServerMove}
    (hae : a <= e)
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenCoherent q a e st.frozen)
    (hcur : ∀ j < st.slots.length,
      requestCoherentCap b (dyadicScale (grayCallDepth q e))
        (familyClientMoveAt
          (grayTailCurrentMove q L e sigma st) j)) :
    GrayChargedFrozenCoherent q a e
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayTailRoundEps q L e st.frozen.length
           slots := st.slots
           move := grayTailCurrentMove q L e sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayTailRoundDelta q L e st.frozen.length) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  cases List.mem_append.mp hp with
  | inl hpOld =>
      exact hst p hpOld j hj
  | inr hpNew =>
      simp only [List.mem_singleton] at hpNew
      subst p
      exact (hcur j hj).mono_cap (grayChargedCallScale_le_spendAlpha hae)


/-- Freezing a spend round preserves coherence of the frozen rounds. -/
lemma grayChargedFrozenCoherent_append_spend
    {q L a e n b pass : Nat} {sigma : FamilyStrategyScheme}
    {m : FamilyServerMove}
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenCoherent q a e st.frozen)
    (hcur : ∀ j < st.slots.length,
      requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt
          (grayChargedSpendMove q L a e pass sigma st) j)) :
    GrayChargedFrozenCoherent q a e
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayChargedSpendEps a L e pass
           slots := st.slots
           move := grayChargedSpendMove q L a e pass sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayChargedSpendDelta a L e pass) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  cases List.mem_append.mp hp with
  | inl hpOld =>
      exact hst p hpOld j hj
  | inr hpNew =>
      simp only [List.mem_singleton] at hpNew
      subst p
      exact hcur j hj

/-- A tail step preserves coherence of the frozen rounds, given coherence of the current move. -/
lemma grayChargedTailStep_frozen_coherent
    {q L a e n b : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hae : a <= e)
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenCoherent q a e st.frozen)
    (hcur : forall _hne : 1 <= st.slots.length,
      ∀ j < st.slots.length,
        requestCoherentCap b (dyadicScale (grayCallDepth q e))
          (familyClientMoveAt
            (grayTailCurrentMove q L e sigma st) j))
    (m : FamilyServerMove) :
    GrayChargedFrozenCoherent q a e
      (grayChargedTailStep q L a e sigma A st m).frozen := by
  unfold grayChargedTailStep grayTailWaitingB
  dsimp only
  by_cases hd : st.done
  · rw [if_pos hd]
    exact hst
  · rw [if_neg hd]
    by_cases hempty : st.slots.isEmpty
    · rw [if_pos hempty]
      exact hst
    · rw [if_neg hempty]
      by_cases hgoal : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
      · rw [if_pos hgoal]
        have hne : 1 <= st.slots.length := by
          cases hs : st.slots with
          | nil => simp [hs] at hempty
          | cons x xs => exact Nat.succ_pos _
        exact grayChargedFrozenCoherent_append hae
          st hst (hcur hne)
      · rw [if_neg hgoal]
        exact hst

/-- A charged step preserves coherence of the frozen rounds, given coherence of the current move
in each phase. -/
lemma grayChargedFrozenCoherent_step
    {q L a e n b : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hae : a <= e)
    (st : GrayChargedState n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenCoherent q a e st.core.frozen)
    (hcur : st.phase = .advantage ->
      forall _hne : 1 <= st.core.slots.length,
        ∀ j < st.core.slots.length,
          requestCoherentCap b (dyadicScale (grayCallDepth q e))
            (familyClientMoveAt
              (grayTailCurrentMove q L e sigma st.core) j))
    (hcurSpend : forall pass, st.phase = .spend pass ->
      1 <= st.core.slots.length ->
      ∀ j < st.core.slots.length,
        requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
          (familyClientMoveAt
            (grayChargedSpendMove q L a e pass sigma st.core) j)) :
    GrayChargedFrozenCoherent q a e
      (grayChargedStep q L a e sigma A st m).core.frozen := by
  unfold grayChargedStep
  cases hphase : st.phase with
  | done =>
      dsimp only
      exact hst
  | advantage =>
      dsimp only
      have hnext := grayChargedTailStep_frozen_coherent
        (a := a) (A := A) hae st.core hst (hcur hphase) m
      by_cases hdone :
          (grayChargedTailStep q L a e sigma A st.core m).done
      · rw [if_pos hdone]
        rw [grayChargedStartSpend_frozen]
        exact hnext
      · rw [if_neg hdone]
        exact hnext
  | spend pass =>
      dsimp only
      by_cases hempty : st.core.slots.isEmpty
      · rw [if_pos hempty]
        exact hst
      · rw [if_neg hempty]
        by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable
            (grayChargedSpendMove q L a e pass sigma st.core)
            (grayTailLocalServerMove
              (grayChargedSpendDelta a L e pass)
              st.core.slots m) = true
        · rw [if_pos hgoal]
          have hne : 1 <= st.core.slots.length := by
            cases hs : st.core.slots with
            | nil => simp [hs] at hempty
            | cons x xs => exact Nat.succ_pos _
          have happ := grayChargedFrozenCoherent_append_spend
            (pass := pass) st.core hst (hcurSpend pass hphase hne) (m := m)
          by_cases hpass : pass + 1 < 8
          · rw [if_pos hpass]
            by_cases hnextempty :
                (grayChargedSlotsForPass q a e (pass + 1)
                  (st.core.frozen ++
                    [{ roundIndex := st.core.frozen.length
                       serverTime := st.core.time
                       epsDepth := grayChargedSpendEps a L e pass
                       slots := st.core.slots
                       move := grayChargedSpendMove q L a e pass sigma st.core
                       allocated := grayTailLocalAllocatedList
                         (grayTailLocalServerMove
                           (grayChargedSpendDelta a L e pass)
                           st.core.slots m)
                       unavailable := st.core.unavailable }])).isEmpty
            · rw [if_pos hnextempty]
              exact happ
            · rw [if_neg hnextempty]
              exact happ
          · rw [if_neg hpass]
            exact happ
        · rw [if_neg hgoal]
          exact hst

/-- Against a legal server play, every round the charged run freezes carries a request coherent
move with cap `dyadicScale (grayChargedSpendAlphaDepth a)`. -/
theorem grayChargedFrozenCoherent_stateAt
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    GrayChargedFrozenCoherent q a e
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen := by
  induction t with
  | zero =>
      intro p hp
      simp only [grayChargedStateAt, grayChargedFold,
        grayChargedInitialState, grayChargedTailInitialState] at hp
      exact (List.not_mem_nil hp).elim
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedFrozenCoherent_step hae
        (grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t)
        (sm t) ih
        (grayChargedCurrentMove_stateAt_coherent
          ha hae hB hRung hsm)
        (grayChargedSpendMove_stateAt_coherent
          hroom hB hRung hsm)

/-- Every source child of every client has frozen son base at most `dyadicScale e`. -/
def GrayChargedSourceBaseCap {n b : Nat}
    (a e : Nat) (st : GrayChargedState n b) : Prop :=
  ∀ i : Fin n, ∀ c : Fin b,
    c.val < grayChargedSourceCount a e ->
      grayTailFrozenSonBase st.core.frozen i c <= dyadicScale e

/-- Freezing a round that only uses spare children preserves the cap `dyadicScale e` on the
frozen son base of the source children. -/
lemma grayChargedSourceBaseCap_append_spare
    {n b a e : Nat} {st : GrayChargedState n b}
    (hcap : GrayChargedSourceBaseCap a e st)
    (p : GrayTailRound n b)
    (hspare : ∀ s ∈ p.slots,
      grayChargedSourceCount a e <= s.2.1.val) :
    ∀ i : Fin n, ∀ c : Fin b,
      c.val < grayChargedSourceCount a e ->
        grayTailFrozenSonBase (st.core.frozen ++ [p]) i c <=
          dyadicScale e := by
  intro i c hc
  rw [grayTailFrozenSonBase_append_global]
  have hzero :
      grayTailSonBase (grayTailSlotEntries p.slots p.move) i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro z hz
    rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    right
    intro heq
    have hge := hspare (p.slots.get j) (List.get_mem _ _)
    have hval : (p.slots.get j).2.1.val = c.val :=
      congrArg Fin.val heq
    omega
  rw [hzero, add_zero]
  exact hcap i c hc

/-- At every time of a charged run the frozen son base of each source child stays at most
`dyadicScale e`. -/
theorem grayChargedSourceBaseCap_stateAt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} :
    GrayChargedSourceBaseCap a e
      (grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      intro i c hc
      simp [grayChargedStateAt,
        grayChargedFold, grayChargedInitialState,
        grayChargedTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase,
        (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      have hcert := grayChargedCertified_stateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t
      generalize hst :
        grayChargedStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t = st at hcert ih ⊢
      cases hcert with
      | advantage core hcore hsource hactive =>
          have hphase : (grayChargedStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).phase = .advantage := by
            rw [hst]
          have hcoreTail := grayChargedStateAt_core_eq_tailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t hphase
          have hcoreTail' : core = grayChargedTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t := by
            simpa [hst] using hcoreTail
          have hnextAll := grayChargedTail_all_frozen_base_le_stateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1)
          rw [grayChargedTailStateAt_succ, ← hcoreTail'] at hnextAll
          simp only [grayChargedStep]
          by_cases hdone :
              (grayChargedTailStep q L a e sigma A core (sm t)).done
          · rw [if_pos hdone]
            intro i c hc
            rw [grayChargedStartSpend_frozen]
            exact hnextAll i c
          · rw [if_neg hdone]
            intro i c hc
            exact hnextAll i c
      | spend pass core hspend =>
          simp only [grayChargedStep]
          by_cases hempty : core.slots.isEmpty
          · rw [if_pos hempty]
            exact ih
          · rw [if_neg hempty]
            by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
                core.slots.length core.unavailable
                (grayChargedSpendMove q L a e pass sigma core)
                (grayTailLocalServerMove
                  (grayChargedSpendDelta a L e pass)
                  core.slots (sm t)) = true
            · rw [if_pos hgoal]
              let p : GrayTailRound n (grayTailBranch q L a e) :=
                { serverTime := core.time
                  roundIndex := core.frozen.length
                  epsDepth := grayChargedSpendEps a L e pass
                  slots := core.slots
                  move := grayChargedSpendMove q L a e pass sigma core
                  allocated := grayTailLocalAllocatedList
                    (grayTailLocalServerMove
                      (grayChargedSpendDelta a L e pass)
                      core.slots (sm t))
                  unavailable := core.unavailable }
              have happ := grayChargedSourceBaseCap_append_spare
                (st := ({ phase := .spend pass, core := core } :
                  GrayChargedState n (grayTailBranch q L a e)))
                ih p (by
                  intro s hs
                  exact grayChargedSpendSlots_son_ge
                    (source := grayChargedSourceCount a e)
                    (count := grayChargedSpendCount q a e)
                    (pass := pass)
                    (threshold := grayChargedThreshold q e)
                    (eps := dyadicScale e)
                    (alpha := dyadicScale a)
                    (frozen := core.frozen)
                    (by
                      have hsCore : s ∈ core.slots := by
                        simpa [p] using hs
                      rw [hspend.slots_eq] at hsCore
                      exact hsCore))
              by_cases hpass : pass + 1 < 8
              · rw [if_pos hpass]
                by_cases hnextempty :
                    (grayChargedSlotsForPass q a e (pass + 1)
                      (core.frozen ++ [p])).isEmpty
                · rw [if_pos hnextempty]
                  simpa [p] using happ
                · rw [if_neg hnextempty]
                  simpa [p] using happ
              · rw [if_neg hpass]
                simpa [p] using happ
            · rw [if_neg hgoal]
              exact ih
      | done core hdone =>
          simpa [grayChargedStep] using ih

end Kolmogorov
