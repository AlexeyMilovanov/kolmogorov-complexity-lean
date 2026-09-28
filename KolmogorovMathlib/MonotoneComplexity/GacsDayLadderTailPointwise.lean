import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAggregate

/-!
# Pointwise terminal bounds for Day's gray-ladder tail

The tail controller only probes the original `2 ^ (e - a)` sons of each
outer root. Recording that support invariant for both the current and frozen
rounds lets us bound the displayed terminal root request by `dyadicScale a`.
Together with the final target-floor adjustment this is exactly the pointwise
window in the hereditary gray certificate.
-/

namespace Kolmogorov

/-- Every open slot, and every slot of a frozen round, sits at a child below `used`. -/
structure GrayTailSourceInvariant {n b : Nat} (used : Nat)
    (st : GrayTailState n b) : Prop where
  current : forall s, s ∈ st.slots -> s.2.1.val < used
  frozen : forall p, p ∈ st.frozen ->
    forall s, s ∈ p.slots -> s.2.1.val < used

/-- The initial tail state satisfies the source invariant `2 ^ (e - a)`. -/
lemma grayTailSourceInvariant_initial (n b a e : Nat)
    (A : Allocation) :
    GrayTailSourceInvariant (2 ^ (e - a))
      (grayTailInitialState n b a e A) := by
  constructor
  · intro s hs
    exact grayTailSlots_used hs
  · simp [grayTailInitialState]

/-- A tail step preserves the source invariant. -/
lemma grayTailSourceInvariant_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailSourceInvariant (2 ^ (e - a)) st) :
    GrayTailSourceInvariant (2 ^ (e - a))
      (grayTailStep q L a e sigma A st sm) := by
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact ⟨hst.current, hst.frozen⟩
  · split
    · exact ⟨hst.current, hst.frozen⟩
    · split
      · constructor
        · intro s hs
          exact grayTailNextSlots_used hs
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hst.frozen p hp
          · simp only [List.mem_singleton] at hp
            subst p
            simpa using hst.current
      · exact ⟨hst.current, hst.frozen⟩

/-- Every state of a tail run satisfies the source invariant `2 ^ (e - a)`. -/
theorem grayTailSourceInvariant_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailSourceInvariant (2 ^ (e - a))
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      exact grayTailSourceInvariant_initial n b a e A
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailSourceInvariant_step q L a e sigma A _ (sm t) ih

/-- A tail run puts no frozen mass on children outside the source range. -/
theorem grayTail_frozen_sonBase_eq_zero_of_source_ge
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (i : Fin n) (c : Fin b) (hc : 2 ^ (e - a) <= c.val) :
    grayTailFrozenSonBase
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen i c = 0 := by
  apply grayTailFrozenSonBase_eq_zero_of_no_round
  intro p hp hson
  obtain ⟨s, hs, _hi, hsc⟩ := hson
  have hsource :=
    (grayTailSourceInvariant_stateAt
      (n := n) (b := b) q L a e sigma A sm t).frozen p hp s hs
  have hval : s.2.1.val = c.val := congrArg Fin.val hsc
  omega

/-- Every frozen entry of a tail run requests a nonnegative amount at the root. -/
theorem grayTail_frozen_entries_root_nonneg
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} :
    forall z, z ∈ grayTailFrozenEntries
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen ->
      0 <= getReq z.2 [] := by
  intro z hz
  unfold grayTailFrozenEntries at hz
  simp only [List.mem_flatMap] at hz
  obtain ⟨p, hp, hz⟩ := hz
  have hvalid := (grayTailCertified_stateAt
    q L a e sigma A sm t).round_valid p hp
  have hpoint :=
    familyRobustGrayGoalAtB.to_pointwise hvalid.2.2.2.2.1
  exact grayTailSlotEntries_root_nonneg
    (halfAmplification_pos q)
    (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
    hpoint z hz

/-- The target floor of the tail is nonnegative. -/
lemma grayTailTargetFloor_nonneg (q a : Nat) :
    (0 : Rat) <= grayTailTargetFloor q a := by
  unfold grayTailTargetFloor
  exact div_nonneg
    (mul_nonneg (by norm_num) (dyadicScale_pos a).le)
    (halfAmplification_pos (q + 1)).le

/-- The target floor of the tail is at most `dyadicScale a`. -/
lemma grayTailTargetFloor_le (q a : Nat) :
    grayTailTargetFloor q a <= dyadicScale a := by
  unfold grayTailTargetFloor
  have hk : (1 : Rat) <= halfAmplification (q + 1) := by
    unfold halfAmplification
    exact le_add_of_nonneg_right
      (div_nonneg (by positivity) (by norm_num))
  have heps := (dyadicScale_pos a).le
  have hden := halfAmplification_pos (q + 1)
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) heps]

/-- In a terminal tail state, every son request lies between `0` and `dyadicScale e`. -/
lemma grayTail_terminal_sonRequest_bounds
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    let st := grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let entries := grayTailEntries st.frozen st.slots
      (if st.done then [] else grayTailCurrentMove q L e sigma st)
    0 <= grayTailSonRequest
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e) entries i c ∧
      grayTailSonRequest
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e) entries i c <= dyadicScale e := by
  dsimp only
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let entries := grayTailEntries st.frozen st.slots
    (if st.done then [] else grayTailCurrentMove q L e sigma st)
  change 0 <= grayTailSonRequest
      (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
      (dyadicScale e) entries i c ∧
    grayTailSonRequest
      (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
      (dyadicScale e) entries i c <= dyadicScale e
  have hbase : grayTailSonBase entries i c =
      grayTailFrozenSonBase st.frozen i c := by
    simpa [st, entries] using
      grayTail_terminal_sonBase_eq_frozen hterminal i c
  simp only [grayTailSonRequest]
  rw [hbase]
  split
  · exact ⟨(dyadicScale_pos e).le, le_rfl⟩
  · exact ⟨grayTailSonBase_nonneg_global (i := i) (c := c)
      (grayTail_frozen_entries_root_nonneg
        (n := n) (b := grayTailBranch q L a e)
        (q := q) (L := L) (a := a) (e := e)
        (t := t) (sigma := sigma) (A := A) (sm := sm)),
      grayTail_all_frozen_base_le_stateAt
        q L a e sigma A sm t i c⟩

/-- In a terminal tail state, children outside the source range carry no request. -/
lemma grayTail_terminal_sonRequest_eq_zero_of_source_ge
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : 2 ^ (e - a) <= c.val) :
    let st := grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let entries := grayTailEntries st.frozen st.slots
      (if st.done then [] else grayTailCurrentMove q L e sigma st)
    grayTailSonRequest
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e) entries i c = 0 := by
  dsimp only
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let entries := grayTailEntries st.frozen st.slots
    (if st.done then [] else grayTailCurrentMove q L e sigma st)
  change grayTailSonRequest
      (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
      (dyadicScale e) entries i c = 0
  have hbase : grayTailSonBase entries i c =
      grayTailFrozenSonBase st.frozen i c := by
    simpa [st, entries] using
      grayTail_terminal_sonBase_eq_frozen hterminal i c
  have hzero : grayTailFrozenSonBase st.frozen i c = 0 := by
    simpa [st] using
      grayTail_frozen_sonBase_eq_zero_of_source_ge
        (q := q) (L := L) (a := a) (e := e)
        (t := t) (sigma := sigma) (A := A) (sm := sm) i c hc
  simp [grayTailSonRequest, hbase, hzero,
    not_lt_of_ge (grayTail_threshold_nonneg_global q e)]

/-- The tail state is either finished or still has an open slot. -/
def GrayTailDoneOrNonempty {n b : Nat}
    (st : GrayTailState n b) : Prop :=
  st.done = true ∨ st.slots ≠ []

/-- The initial tail state of a nonempty family has an open slot. -/
lemma grayTailDoneOrNonempty_initial
    {n q L a e : Nat} (hn : 1 <= n) (A : Allocation) :
    GrayTailDoneOrNonempty
      (grayTailInitialState n (grayTailBranch q L a e) a e A) := by
  right
  intro hnil
  have hb : 0 < grayTailBranch q L a e := by
    exact lt_of_lt_of_le (by omega)
      (two_le_ladderBranching (le_max_left 2 _) a e)
  let i : Fin n := ⟨0, by omega⟩
  let c : Fin (grayTailBranch q L a e) := ⟨0, hb⟩
  have hson := grayTailHasSon_slots
    (n := n) (b := grayTailBranch q L a e)
    (used := 2 ^ (e - a)) (round := 0) hb i c (by positivity)
  obtain ⟨s, hs, _⟩ := hson
  have hnil' :
      grayTailSlots n (grayTailBranch q L a e) (2 ^ (e - a)) 0 = [] := by
    simpa [grayTailInitialState] using hnil
  rw [hnil'] at hs
  simp at hs

/-- A tail step keeps the state either finished or holding an open slot. -/
lemma grayTailDoneOrNonempty_step {n b q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {st : GrayTailState n b} (sm : FamilyServerMove)
    (hst : GrayTailDoneOrNonempty st) :
    GrayTailDoneOrNonempty (grayTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · simp [grayTailWaitingB] at hw
  · by_cases hd : st.done = true
    · simp [grayTailStep, hw, hd, GrayTailDoneOrNonempty]
    · by_cases hs : st.slots.isEmpty = true
      · simpa [grayTailStep, hw, hd, hs, GrayTailDoneOrNonempty] using hst
      · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
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
          let candidates := grayTailNextSlots e (2 ^ (e - a))
            frozen'.length threshold A frozen' sm
          let stop := grayTailGlobalQuarterB (n := n) (2 ^ (e - a)) candidates
          unfold GrayTailDoneOrNonempty
          by_cases hstop : stop = true
          · left
            have hfinished :
                grayTailGlobalQuarterB (n := n) (2 ^ (e - a)) candidates = true ∨
                  grayTailRoundCount q <= frozen'.length :=
              Or.inl hstop
            simpa [grayTailStep, grayTailWaitingB, hw, hd, hs, hg, p, frozen',
              threshold, candidates, stop, hstop] using hfinished
          · right
            have hcandidates : candidates ≠ [] := by
              intro hnil
              apply hstop
              simp [stop, grayTailGlobalQuarterB, hnil]
            simpa [grayTailStep, grayTailWaitingB, hw, hd, hs, hg, p, frozen',
              threshold, candidates, stop] using hcandidates
        · simpa [grayTailStep, hw, hd, hs, hg, GrayTailDoneOrNonempty] using hst

/-- Every state of a tail run over a nonempty family is either finished or holds an open slot. -/
theorem grayTailDoneOrNonempty_stateAt
    {n q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n) (t : Nat) :
    GrayTailDoneOrNonempty
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayTailDoneOrNonempty_initial hn A
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailDoneOrNonempty_step (sm t) ih

/-- A terminal tail state over a nonempty family is finished, not merely out of slots. -/
theorem grayTail_done_of_terminal
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done = true := by
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  rcases grayTailDoneOrNonempty_stateAt
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) hn t with hdone | hnonempty
  · simpa [st] using hdone
  · by_contra h
    have hdoneFalse : st.done = false := Bool.eq_false_of_not_eq_true (by
      simpa [st] using h)
    have hempty : st.slots.isEmpty = true := by
      simpa [st, hdoneFalse] using hterminal
    exact hnonempty (List.isEmpty_iff.mp hempty)

/-- In a terminal tail state, the son requests of a client sum to at most `dyadicScale a`. -/
lemma grayTail_terminal_sonRequest_sum_le
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (i : Fin n) :
    let st := grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let entries := grayTailEntries st.frozen st.slots
      (if st.done then [] else grayTailCurrentMove q L e sigma st)
    (∑ c : Fin (grayTailBranch q L a e),
      grayTailSonRequest
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e) entries i c) <= dyadicScale a := by
  dsimp only
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let entries := grayTailEntries st.frozen st.slots
    (if st.done then [] else grayTailCurrentMove q L e sigma st)
  let used := 2 ^ (e - a)
  calc
    (∑ c : Fin (grayTailBranch q L a e),
        grayTailSonRequest
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
          (dyadicScale e) entries i c) <=
        ∑ c : Fin (grayTailBranch q L a e),
          if c.val < used then dyadicScale e else 0 := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : c.val < used
      · simpa [used, hc, st, entries] using
          (grayTail_terminal_sonRequest_bounds
            (q := q) (L := L) (a := a) (e := e)
            (t := t) (sigma := sigma) (A := A) (sm := sm)
            hterminal i c).2
      · have hzero :=
          grayTail_terminal_sonRequest_eq_zero_of_source_ge
            (q := q) (L := L) (a := a) (e := e)
            (t := t) (sigma := sigma) (A := A) (sm := sm)
            hterminal i c (by simpa [used] using Nat.le_of_not_gt hc)
        simpa [used, hc, st, entries] using hzero.le
    _ = ∑ c ∈ (Finset.univ.filter
          (fun c : Fin (grayTailBranch q L a e) => c.val < used)),
          dyadicScale e := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter
          (fun c : Fin (grayTailBranch q L a e) =>
            c.val < used)).card : Rat) * dyadicScale e := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (used : Rat) * dyadicScale e := by
      apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
      exact_mod_cast
        grayTail_source_fin_card_le (grayTailBranch q L a e) used
    _ = dyadicScale a := by
      simpa [used] using two_pow_sub_mul_dyadicScale hae

/-- The tail output requests at the root of a client the root request computed from its entries. -/
lemma getFamilyReq_grayTailOutput_root
    {n b q L a e i : Nat} {sigma : FamilyStrategyScheme}
    (st : GrayTailState n b) (hi : i < n) :
    getFamilyReq (grayTailOutput q L a e sigma st) i [] =
      grayTailRootRequest st.done (grayTailTargetFloor q a)
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        (dyadicScale e)
        (grayTailEntries st.frozen st.slots
          (if st.done then [] else grayTailCurrentMove q L e sigma st))
        ⟨i, hi⟩ := by
  unfold grayTailOutput grayTailFamilyMove getFamilyReq familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- A finished tail run requests, at each client root, between the target floor and
`dyadicScale a`. -/
theorem grayTail_terminal_root_window_of_done
    {n q L a e t i : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (hi : i < n)
    (hdone : (grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done = true) :
    grayTailTargetFloor q a <=
        getFamilyReq
          (grayTailOutput q L a e sigma
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) i [] ∧
      getFamilyReq
          (grayTailOutput q L a e sigma
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) i [] <= dyadicScale a := by
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have hterminal : (st.done || st.slots.isEmpty) = true := by
    simp [st, hdone]
  rw [getFamilyReq_grayTailOutput_root st hi]
  unfold grayTailRootRequest
  rw [if_pos]
  · constructor
    · exact le_max_right _ _
    · apply max_le
      · simpa [st] using
          grayTail_terminal_sonRequest_sum_le
            (q := q) (L := L) (a := a) (e := e)
            (t := t) (sigma := sigma) (A := A) (sm := sm)
            hae hterminal ⟨i, hi⟩
      · exact grayTailTargetFloor_le q a
  · simpa [st] using hdone

/-- A finished tail run meets the pointwise gray goal at amplification
`halfAmplification (q + 1)` and level `(3/4) * dyadicScale a`. -/
theorem grayTail_terminal_pointwise_of_done
    {n q L a e t epsDepth deltaDepth : Nat}
    {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (hdone : (grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done = true)
    (server : FamilyServerMove) :
    familyPointwiseGrayAtB (halfAmplification (q + 1))
      ((3 / 4 : Rat) * dyadicScale a) epsDepth deltaDepth n A
      (grayTailOutput q L a e sigma
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t))
      server = true := by
  unfold familyPointwiseGrayAtB
  rw [List.all_eq_true]
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  have hwindow := grayTail_terminal_root_window_of_done
    (q := q) (L := L) (a := a) (e := e)
    (t := t) (sigma := sigma) (A := A) (sm := sm)
    hae hin hdone
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · have hkpos := halfAmplification_pos (q + 1)
    calc
      (3 / 4 : Rat) * dyadicScale a =
          halfAmplification (q + 1) * grayTailTargetFloor q a := by
            unfold grayTailTargetFloor
            field_simp
      _ <= halfAmplification (q + 1) *
          getFamilyReq
            (grayTailOutput q L a e sigma
              (grayTailStateAt
                (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm t)) i [] :=
        mul_le_mul_of_nonneg_left hwindow.1 hkpos.le
  · calc
      getFamilyReq
          (grayTailOutput q L a e sigma
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) i [] <= dyadicScale a := hwindow.2
      _ = (4 / 3 : Rat) * ((3 / 4 : Rat) * dyadicScale a) := by ring


/-- A terminal tail run over a nonempty family meets the pointwise gray goal at amplification
`halfAmplification (q + 1)` and level `(3/4) * dyadicScale a`. -/
theorem grayTail_terminal_pointwise
    {n q L a e t epsDepth deltaDepth : Nat}
    {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n) (hae : a <= e)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (server : FamilyServerMove) :
    familyPointwiseGrayAtB (halfAmplification (q + 1))
      ((3 / 4 : Rat) * dyadicScale a) epsDepth deltaDepth n A
      (grayTailOutput q L a e sigma
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t))
      server = true := by
  apply grayTail_terminal_pointwise_of_done hae
  · exact grayTail_done_of_terminal hn hterminal

end Kolmogorov
