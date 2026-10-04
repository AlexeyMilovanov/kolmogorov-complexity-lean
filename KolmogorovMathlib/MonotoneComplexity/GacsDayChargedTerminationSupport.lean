import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore

/-!
# Finite phase support for the charged Gacs-Day controller

These lemmas isolate the purely finite controller argument used by closure
leaf L3.  They do not use any mathematical leaf beyond the supplied
`GrayChargedSpendProgress` hypothesis.
-/

namespace Kolmogorov

/-- The initial charged tail state of a nonempty family is either finished or has an open slot. -/
lemma grayChargedTailDoneOrNonempty_initial
    {n q L a e : Nat} (hn : 1 <= n) (A : Allocation) :
    GrayTailDoneOrNonempty
      (grayChargedTailInitialState n (grayTailBranch q L a e) a e A) := by
  right
  intro hnil
  have hb : 0 < grayTailBranch q L a e := by
    exact lt_of_lt_of_le (by omega)
      (two_le_ladderBranching (le_max_left 2 _) a e)
  let i : Fin n := ⟨0, by omega⟩
  let c : Fin (grayTailBranch q L a e) := ⟨0, hb⟩
  have hson := grayTailHasSon_slots
    (n := n) (b := grayTailBranch q L a e)
    (used := grayChargedSourceCount a e) (round := 0) hb i c (by
      change 0 < grayChargedSourceCount a e
      simp [grayChargedSourceCount])
  obtain ⟨s, hs, _⟩ := hson
  have hnil' :
      grayTailSlots n (grayTailBranch q L a e)
          (grayChargedSourceCount a e) 0 = [] := by
    simpa [grayChargedTailInitialState] using hnil
  rw [hnil'] at hs
  simp at hs

/-- A charged tail step keeps the state either finished or holding an open slot. -/
lemma grayChargedTailDoneOrNonempty_step
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {st : GrayTailState n b} (sm : FamilyServerMove)
    (hst : GrayTailDoneOrNonempty st) :
    GrayTailDoneOrNonempty (grayChargedTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · simp [grayTailWaitingB] at hw
  · by_cases hd : st.done = true
    · simp [grayChargedTailStep, hw, hd, GrayTailDoneOrNonempty]
    · by_cases hs : st.slots.isEmpty = true
      · simpa [grayChargedTailStep, hw, hd, hs, GrayTailDoneOrNonempty] using hst
      · by_cases hg : grayChargedTailGoalAtB q e
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length st.unavailable
            (grayTailCurrentMove q L e sigma st)
            (grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots sm) = true
        · let p : GrayTailRound n b :=
            { serverTime := st.time
              roundIndex := st.frozen.length
              epsDepth := grayTailRoundEps q L e st.frozen.length
              slots := st.slots
              move := grayTailCurrentMove q L e sigma st
              allocated := grayTailLocalAllocatedList
                (grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots sm)
              unavailable := st.unavailable }
          let frozen' := st.frozen ++ [p]
          let threshold := dyadicScale e -
            dyadicScale e / (6 * halfAmplification q)
          let candidates := grayTailNextSlots e
            (grayChargedSourceCount a e) frozen'.length threshold A frozen' sm
          by_cases hcandidates : candidates = []
          · left
            have hquarter : grayTailGlobalQuarterB
                (n := n) (grayChargedSourceCount a e) candidates = true := by
              simp [grayTailGlobalQuarterB, hcandidates]
            have hfinished :
                grayTailGlobalQuarterB (n := n)
                    (grayChargedSourceCount a e) candidates = true ∨
                  grayChargedAdvantageRoundCount q <= frozen'.length :=
              Or.inl hquarter
            simpa [grayChargedTailStep, grayTailWaitingB, hw, hd, hs, hg,
              p, frozen', threshold, candidates] using hfinished
          · right
            simpa [grayChargedTailStep, grayTailWaitingB, hw, hd, hs, hg,
              p, frozen', threshold, candidates] using hcandidates
        · simpa [grayChargedTailStep, hw, hd, hs, hg,
            GrayTailDoneOrNonempty] using hst

/-- Every state of a charged tail run over a nonempty family is either finished or holds an open
slot. -/
theorem grayChargedTailDoneOrNonempty_stateAt
    {n q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n) (t : Nat) :
    GrayTailDoneOrNonempty
      (grayChargedTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedTailDoneOrNonempty_initial hn A
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTailDoneOrNonempty_step (sm t) ih

/-- A terminal charged tail state over a nonempty family is finished, not merely out of slots. -/
theorem grayChargedTail_done_of_terminal
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n)
    (hterminal : ((grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done = true := by
  let st := grayChargedTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  rcases grayChargedTailDoneOrNonempty_stateAt
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) hn t with hdone | hnonempty
  · simpa [st] using hdone
  · by_contra h
    have hdoneFalse : st.done = false := Bool.eq_false_of_not_eq_true (by
      simpa [st] using h)
    have hempty : st.slots.isEmpty = true := by
      simpa [st, hdoneFalse] using hterminal
    exact hnonempty (List.isEmpty_iff.mp hempty)

/-- Under the source invariant the son base of a spare child is zero. -/
lemma grayTailSonBase_eq_zero_of_sourceInvariant
    {n b source : Nat} {st : GrayTailState n b}
    (hsource : GrayTailSourceInvariant source st)
    (current : FamilyClientMove) (i : Fin n) (c : Fin b)
    (hc : source <= c.val) :
    grayTailSonBase (grayTailEntries st.frozen st.slots current) i c = 0 := by
  unfold grayTailEntries
  rw [grayTailSonBase_append_globalEntries]
  have hfrozen :
      grayTailSonBase (grayTailFrozenEntries st.frozen) i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro z hz
    rw [grayTailFrozenEntries, List.mem_flatMap] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    right
    intro hmatch
    have hmem : p.slots.get j ∈ p.slots := List.get_mem _ _
    have hlt := hsource.frozen p hp (p.slots.get j) hmem
    have hval : (p.slots.get j).2.1.val = c.val :=
      congrArg Fin.val hmatch
    omega
  have hslots : grayTailSonBase
      (grayTailSlotEntries st.slots current) i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro z hz
    rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    right
    intro hmatch
    have hmem : st.slots.get j ∈ st.slots := List.get_mem _ _
    have hlt := hsource.current (st.slots.get j) hmem
    have hval : (st.slots.get j).2.1.val = c.val :=
      congrArg Fin.val hmatch
    omega
  rw [hfrozen, hslots, add_zero]

/-- Under the source invariant the charged son request agrees with the plain tail son request at
every child. -/
lemma grayChargedSonRequest_eq_grayTailSonRequest_of_sourceInvariant
    {n b source : Nat} {st : GrayTailState n b}
    (hsource : GrayTailSourceInvariant source st)
    (threshold eps : Rat) (hthreshold : 0 <= threshold)
    (current : FamilyClientMove) (i : Fin n) (c : Fin b) :
    grayChargedSonRequest source threshold eps
        (grayTailEntries st.frozen st.slots current) i c =
      grayTailSonRequest threshold eps
        (grayTailEntries st.frozen st.slots current) i c := by
  by_cases hc : c.val < source
  · simp [grayChargedSonRequest, hc]
  · have hbase := grayTailSonBase_eq_zero_of_sourceInvariant
      hsource current i c (Nat.le_of_not_gt hc)
    simp [grayChargedSonRequest, grayTailSonRequest, hc, hbase,
      not_lt_of_ge hthreshold]

/-- Under the source invariant the charged displayed move agrees with the plain tail move. -/
lemma grayChargedTailFamilyMove_eq_grayTailFamilyMove_of_sourceInvariant
    {n b source : Nat} {st : GrayTailState n b}
    (hsource : GrayTailSourceInvariant source st)
    (targetFloor threshold eps : Rat) (hthreshold : 0 <= threshold)
    (current : FamilyClientMove) :
    grayChargedTailFamilyMove source threshold eps
        st.frozen st.slots current =
      grayTailFamilyMove false targetFloor threshold eps
        st.frozen st.slots current := by
  unfold grayChargedTailFamilyMove grayTailFamilyMove
  dsimp
  apply congrArg
    (fun f : Fin n -> ClientMove => List.ofFn f)
  funext i
  unfold graftTwoLevel
  dsimp
  congr 1
  · unfold grayChargedRootRequest grayTailRootRequest
    dsimp
    congr 1
    ext c
    exact grayChargedSonRequest_eq_grayTailSonRequest_of_sourceInvariant
      hsource threshold eps hthreshold current i c
  · funext c
    by_cases hc : c < b
    · simp only [dite_eq_left hc]
      rw [grayChargedSonRequest_eq_grayTailSonRequest_of_sourceInvariant
        hsource threshold eps hthreshold current i ⟨c, hc⟩]
    · simp [hc]

/-- While the controller is in the `advantage` phase, the charged strategy plays the output of
the underlying tail state. -/
lemma playClientFamily_grayChargedStrategy_eq_advantageOutput
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hn : 1 <= n)
    (hphase : (grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T).phase = .advantage) :
    playClientFamily A n (grayChargedStrategy q L a e sigma) sm T =
      grayChargedTailOutput q L a e sigma
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm T) := by
  let st := grayChargedTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm T
  have hcore := grayChargedStateAt_core_eq_tailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm T hphase
  have hdone : st.done = false := by
    have hactive := grayChargedRunState_core_done_false_of_advantage
      (q := q) (L := L) (a := a) (e := e)
      (n := n) (t := T) (sigma := sigma) (A := A) (sm := sm) hphase
    change (grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T).core.done = false at hactive
    rw [hcore] at hactive
    exact hactive
  have hslots : st.slots.isEmpty = false := by
    rcases grayChargedTailDoneOrNonempty_stateAt
        (q := q) (L := L) (a := a) (e := e)
        (sigma := sigma) (A := A) (sm := sm) hn T with hdone' | hnonempty
    · rw [hdone] at hdone'
      contradiction
    · apply Bool.eq_false_of_not_eq_true
      intro hempty
      exact hnonempty (List.isEmpty_iff.mp hempty)
  have hsource := grayChargedTailSourceInvariant_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm T
  rw [playClientFamily_grayChargedStrategy]
  unfold grayChargedDisplayedMove
  dsimp
  rw [hphase, hcore]
  dsimp
  rw [hslots]
  unfold grayChargedTailOutput grayTailOutput
  rw [hdone]
  dsimp
  exact grayChargedTailFamilyMove_eq_grayTailFamilyMove_of_sourceInvariant
    hsource (grayTailTargetFloor q a) (grayChargedThreshold q e)
      (dyadicScale e) (grayTail_threshold_nonneg_global q e)
      (grayTailCurrentMove q L e sigma st)

/-- Past the eighth pass a charged step either stays in that pass or finishes. -/
lemma grayChargedStep_spend_phase_of_ge
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedState n b} {pass : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass) (hpass : 8 <= pass) :
    (grayChargedStep q L a e sigma A st sm).phase = .spend pass ∨
      (grayChargedStep q L a e sigma A st sm).phase = .done := by
  simp only [grayChargedStep, hst]
  have hlt : ¬ (pass + 1 < 8) := by omega
  split
  · exact Or.inr rfl
  · split
    · right
      simp
    · exact Or.inl rfl

/-- From a spend pass a charged step stays in the pass, moves to the next one, or finishes. -/
lemma grayChargedStep_spend_phase
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedState n b} {pass : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass) :
    (grayChargedStep q L a e sigma A st sm).phase = .spend pass ∨
      (grayChargedStep q L a e sigma A st sm).phase = .spend (pass + 1) ∨
      (grayChargedStep q L a e sigma A st sm).phase = .done := by
  simp only [grayChargedStep, hst]
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · split
      · split
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- Given progress in every spend pass and enough fuel for the remaining passes, the run either
wins with positive unserved mass or reaches the `done` phase. -/
lemma grayCharged_spend_pass_loop
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hprogress : GrayChargedSpendProgress q L a e n sigma A sm)
    (fuel pass t : Nat)
    (hfuel : 8 - pass <= fuel)
    (hst : (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .spend pass) :
    GrayChargedPositive q L a e n sigma A sm ∨
      exists d, (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm d).phase = .done := by
  induction fuel generalizing pass t with
  | zero =>
      have hpass4 : 8 <= pass := by omega
      rcases hprogress t pass hst with hpos | ⟨u, htu, hu⟩
      · exact Or.inl hpos
      · have hex : exists w, t < w ∧
            (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm w).phase ≠ .spend pass :=
          ⟨u + 1, by omega, hu⟩
        let w := Nat.find hex
        have hw_spec := Nat.find_spec hex
        have hw_min : forall j, t < j -> j < Nat.find hex ->
            (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm j).phase = .spend pass := by
          intro j ht hj
          have h := Nat.find_min hex hj
          tauto
        have hpred_lt : w - 1 < w := by omega
        have hprev : (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (w - 1)).phase = .spend pass := by
          by_cases htw : t = w - 1
          · rw [← htw]
            exact hst
          · have htlt : t < w - 1 := by omega
            exact hw_min (w - 1) htlt hpred_lt
        have hstep : grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm w =
          grayChargedStep q L a e sigma A
            (grayChargedStateAt q L a e sigma A sm (w - 1)) (sm (w - 1)) := by
          rw [← grayChargedStateAt_succ]
          congr 1
          omega
        rcases grayChargedStep_spend_phase_of_ge (L := L) hprev hpass4 with
          hsame | hdone
        · exfalso
          apply hw_spec.2
          rw [hstep, hsame]
        · exact Or.inr ⟨w, by rw [hstep, hdone]⟩
  | succ fuel ih =>
      rcases hprogress t pass hst with hpos | ⟨u, htu, hu⟩
      · exact Or.inl hpos
      · have hex : exists w, t < w ∧
            (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm w).phase ≠ .spend pass :=
          ⟨u + 1, by omega, hu⟩
        let w := Nat.find hex
        have hw_spec := Nat.find_spec hex
        have hw_min : forall j, t < j -> j < Nat.find hex ->
            (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm j).phase = .spend pass := by
          intro j ht hj
          have h := Nat.find_min hex hj
          tauto
        have hpred_lt : w - 1 < w := by omega
        have hprev : (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (w - 1)).phase = .spend pass := by
          by_cases htw : t = w - 1
          · rw [← htw]
            exact hst
          · have htlt : t < w - 1 := by omega
            exact hw_min (w - 1) htlt hpred_lt
        have hstep : grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm w =
          grayChargedStep q L a e sigma A
            (grayChargedStateAt q L a e sigma A sm (w - 1)) (sm (w - 1)) := by
          rw [← grayChargedStateAt_succ]
          congr 1
          omega
        by_cases hpass4 : pass < 8
        · rcases grayChargedStep_spend_phase (L := L) hprev with
            hsame | hnext | hdone
          · exfalso
            apply hw_spec.2
            rw [hstep, hsame]
          · have hw_phase :
                (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm w).phase = .spend (pass + 1) := by
              rw [hstep, hnext]
            have hfuel' : 8 - (pass + 1) <= fuel := by omega
            exact ih (pass + 1) w hfuel' hw_phase
          · exact Or.inr ⟨w, by rw [hstep, hdone]⟩
        · rcases grayChargedStep_spend_phase_of_ge (L := L) hprev (by omega) with
            hsame | hdone
          · exfalso
            apply hw_spec.2
            rw [hstep, hsame]
          · exact Or.inr ⟨w, by rw [hstep, hdone]⟩

end Kolmogorov
