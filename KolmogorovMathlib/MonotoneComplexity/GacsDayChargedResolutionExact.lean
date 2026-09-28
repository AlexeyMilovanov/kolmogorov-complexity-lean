import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay

/-!
# Exact reserve exits for the charged advantage controller

The charged acceptance test directly supplies the nonnegative root requests
used by the reserve chronology.  This module ports the exact-resolution
invariant to the executable charged advantage phase without assuming the
stronger robust pointwise interface.
-/

namespace Kolmogorov

/-- The advantage round budget is smaller than the branching of the tail, so a fresh child is
available for every round. -/
lemma grayChargedAdvantageRoundCount_lt_grayTailBranch (q L a e : Nat) :
    grayChargedAdvantageRoundCount q < grayTailBranch q L a e := by
  have hbase : grayTailBaseBranch q L <= grayTailBranch q L a e := by
    simp [grayTailBranch, ladderBranching]
  refine lt_of_lt_of_le ?_ hbase
  rw [grayChargedAdvantageRoundCount_eq, grayTailBaseBranch]
  have hq : q + 1 <
      2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
    calc
      q + 1 < 2 ^ (q + 1) := Nat.lt_two_pow_self
      _ <= 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith [Nat.zero_le (256 * (q + 1) ^ 2 * L)]
  have hfull : 256 * (q + 1) ^ 2 <
      256 * (q + 1) *
        2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
    calc
      256 * (q + 1) ^ 2 = (256 * (q + 1)) * (q + 1) := by ring
      _ < (256 * (q + 1)) *
          2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
        have hfactor : 0 < 256 * (q + 1) :=
          Nat.mul_pos (by norm_num) (Nat.succ_pos q)
        exact Nat.mul_lt_mul_of_pos_left hq hfactor
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (Nat.sub_le (256 * (q + 1) ^ 2) 8) hfull)
    (le_max_right _ _)

/-- Every source child is in exactly one of three states: still open with a fresh checkpoint,
closed by exceeding the service threshold, or closed with a persistent reserve below the
threshold. -/
def GrayChargedExactResolutionInvariant {n b : Nat} (q e a : Nat)
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

/-- Exact resolution invariant preservation for an active child during a charged tail step. -/
private lemma grayChargedExactResolutionInvariant_step_active
    {n b q a e t : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailState n b) (p : GrayTailRound n b) (i : Fin n) (c : Fin b)
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

/-- Exact resolution invariant preservation for a resolved child during a charged tail step:
a child already closed by the threshold stays closed, and one closed by a persistent reserve
either reopens with a fresh checkpoint or stays closed. -/
private lemma grayChargedExactResolutionInvariant_step_resolved
    {n b q a e t : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailState n b) (p : GrayTailRound n b) (i : Fin n) (c : Fin b)
    (hused : c.val < 2 ^ (e - a))
    (haccept : GrayTailAcceptedRound st p t)
    (hnonneg : forall z, z ∈ grayTailSlotEntries p.slots p.move -> 0 <= getReq z.2 [])
    (hresolved : GrayTailChildThresholdClosed q e A sm st.frozen st.slots i c ∨
      GrayTailChildReserveClosed q e A sm st.frozen st.slots i c) :
    let frozen' : GrayTailFrozen n b := st.frozen ++ [p]
    let threshold := grayTailExitThreshold q e
    let candidates := grayTailNextSlots e (2 ^ (e - a))
      frozen'.length threshold A frozen' (sm t)
    GrayTailChildOpen e A sm frozen' candidates i c ∨
      GrayTailChildThresholdClosed q e A sm frozen' candidates i c ∨
      GrayTailChildReserveClosed q e A sm frozen' candidates i c := by
  intro frozen' threshold candidates
  obtain ⟨hp_time, hp_slots, htime, hbefore, hr⟩ := haccept
  rcases hresolved with ⟨hthreshold, htexit, hinactive⟩ | ⟨hexit, hbasecap, hinactive⟩
  · right; left
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
    refine ⟨hthreshold', htexit.append hpnone, ?_⟩
    intro hn
    have hbelow := ((grayTailHasSon_next_iff hr i c).1 hn).2.1
    exact hbelow hthreshold'
  · have hpnone : ¬ GrayTailRoundHasSon p i c := by
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
    · right; right
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

/-- A charged tail step preserves the exact resolution invariant. -/
lemma grayChargedExactResolutionInvariant_step
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailState n b) (htime : st.time = t)
    (hbefore : forall p, p ∈ st.frozen -> p.serverTime < t)
    (hround : (st.done || st.slots.isEmpty) ≠ true ->
      st.frozen.length + 1 < b)
    (hprev : GrayChargedExactResolutionInvariant q e a A sm st) :
    GrayChargedExactResolutionInvariant q e a A sm
      (grayChargedTailStep q L a e sigma A st (sm t)) := by
  intro i c hused
  unfold grayChargedTailStep
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
        let next := candidates
        change (GrayTailHasSon next i c ∧
            GrayTailFreshCheckpoint e A sm frozen' i c) ∨
          (threshold < grayTailFrozenSonBase frozen' i c ∧
            GrayTailThresholdExit e A sm frozen' i c ∧
            ¬ GrayTailHasSon next i c) ∨
            (GrayTailPersistentReserveExit e A sm frozen' i c ∧
              grayTailFrozenSonBase frozen' i c <= threshold ∧
              ¬ GrayTailHasSon next i c)
        have hcharged : familyChargedGrayGoalAtB 4 (halfAmplification q)
            (dyadicScale (grayCallDepth q e))
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length st.unavailable
            (grayTailCurrentMove q L e sigma st)
            (grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) = true := by
          simpa [grayChargedTailGoalAtB] using hgoal
        obtain ⟨G, _hGmem, hG⟩ :=
          familyChargedGrayGoalAtB.exists_charge hcharged
        have hnonneg : forall z, z ∈ grayTailSlotEntries p.slots p.move ->
            0 <= getReq z.2 [] := by
          intro z hz
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
          have hj := (familyGrayChargeAtB.root hG j.isLt).1
          unfold getFamilyReq at hj
          have halpha : 0 <= dyadicScale (grayCallDepth q e) / 2 :=
            (div_pos (dyadicScale_pos _) (by norm_num)).le
          simpa [p] using le_trans halpha hj
        have hr : frozen'.length < b := by
          dsimp [frozen']
          simpa using hround hactive
        have haccept : GrayTailAcceptedRound st p t :=
          ⟨rfl, rfl, htime, hbefore, hr⟩
        rcases hprev i c hused with hopen | hresolved
        · exact grayChargedExactResolutionInvariant_step_active st p i c hused
            haccept hopen
        · exact grayChargedExactResolutionInvariant_step_resolved st p i c hused
            haccept hnonneg hresolved
      next _ => simpa using hprev i c hused

/-- Every state of a charged tail run satisfies the exact resolution invariant. -/
theorem grayChargedExactResolutionInvariant_stateAt
    {n q L a e : Nat} (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedExactResolutionInvariant q e a A sm
      (grayChargedTailStateAt
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
      rw [grayChargedTailStateAt_succ]
      apply grayChargedExactResolutionInvariant_step
        (t := t) (sm := sm) _
      · exact (grayChargedTailCertified_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).time_eq
      · intro p hp
        exact (grayChargedTailCertified_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).round_valid p hp |>.2.2.1
      · intro hactive
        have hcert := grayChargedTailCertified_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t
        have hdoneFalse : (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).done = false := by
          cases hdone : (grayChargedTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).done with
          | false => rfl
          | true =>
              exfalso
              apply hactive
              simp [hdone]
        have hlen : (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length <
            grayChargedAdvantageRoundCount q :=
          hcert.frozen_bound.2 hdoneFalse
        have hbranch : grayChargedAdvantageRoundCount q <
            grayTailBranch q L a e :=
          grayChargedAdvantageRoundCount_lt_grayTailBranch q L a e
        omega
      · exact ih

/-- In a terminal tail state, every source child without an open slot either exceeds the service
threshold or carries a persistent reserve. -/
theorem grayChargedTail_terminal_exact_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (_hterminal : ((grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) ->
      ¬ GrayTailHasSon
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots i c ->
      (dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
        grayTailFrozenSonBase
          (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c) ∨
      GrayTailPersistentReserveExit e A sm
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).frozen i c := by
  intro i c hused hinactive
  have hinv := grayChargedExactResolutionInvariant_stateAt
    (n := n) sigma A sm t i c hused
  rcases hinv with hactive | hresolved
  · exact (hinactive hactive.1).elim
  · rcases hresolved with ⟨hthreshold, _htexit, _⟩ |
      ⟨hexit, _hbasecap, _⟩
    · exact Or.inl hthreshold
    · exact Or.inr hexit

/-- Terminal resolution retaining the last-call certificate required by the
geometric accounting. -/
theorem grayChargedTail_terminal_detailed_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (_hterminal : ((grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) ->
      ¬ GrayTailHasSon
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots i c ->
      ((dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailFrozenSonBase
            (grayChargedTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).frozen i c) ∧
        GrayTailThresholdExit e A sm
          (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c) ∨
      (GrayTailPersistentReserveExit e A sm
          (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen i c ∧
        grayTailFrozenSonBase
            (grayChargedTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).frozen i c <=
          dyadicScale e - dyadicScale e /
            (6 * halfAmplification q)) := by
  intro i c hused hinactive
  have hinv := grayChargedExactResolutionInvariant_stateAt
    (n := n) sigma A sm t i c hused
  rcases hinv with hactive | hresolved
  · exact (hinactive hactive.1).elim
  · rcases hresolved with ⟨hthreshold, htexit, _⟩ |
      ⟨hexit, hbasecap, _⟩
    · exact Or.inl ⟨hthreshold, htexit⟩
    · exact Or.inr ⟨hexit, hbasecap⟩

end Kolmogorov
