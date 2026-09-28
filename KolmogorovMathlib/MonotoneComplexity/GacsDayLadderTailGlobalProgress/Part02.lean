import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRound
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part01

/-!
# The tail run exhausts its round budget

The termination side of the global accounting. Every open slot stays below the service threshold
(`grayTail_active_base_le_step_global`, `grayTail_active_base_le_stateAt_global`) and every
frozen son base below `dyadicScale e` (`grayTail_all_frozen_base_le_step`,
`grayTail_all_frozen_base_le_stateAt`), the scale arithmetic being
`grayTail_callScale_add_threshold_le`; the counting bound `grayTail_source_fin_card_le` limits
how many children a client can still use. Since each round consumes budget that these bounds cap,
`grayTail_slots_eq_nil_of_roundCount_stateAt_global` concludes that once the round budget is
spent the run has no open slots left.
-/

namespace Kolmogorov
open scoped BigOperators

/-- A tail step keeps every open slot below the service threshold. -/
lemma grayTail_active_base_le_step_global
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove)
    (hprev : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase st.frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall s, s ∈ (grayTailStep q L a e sigma A st sm).slots ->
      grayTailFrozenSonBase
          (grayTailStep q L a e sigma A st sm).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hprev
  · split
    · exact hprev
    · split
      · intro s hs
        exact grayTailNextSlots_base_le_global hs
      · exact hprev
/-- At every time of a tail run, every open slot is below the service threshold. -/
theorem grayTail_active_base_le_stateAt_global
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall s, s ∈ (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots ->
      grayTailFrozenSonBase
          (grayTailStateAt (n := n) (b := b)
            q L a e sigma A sm t).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  induction t with
  | zero =>
      intro s hs
      simpa [grayTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase] using
        grayTail_threshold_nonneg_global q e
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTail_active_base_le_step_global q L a e sigma A _ (sm t) ih

/-- One more call at scale `dyadicScale (grayCallDepth q e)` still fits under `dyadicScale e`
above the service threshold. -/
lemma grayTail_callScale_add_threshold_le (q e : Nat) :
    dyadicScale e - dyadicScale e / (6 * halfAmplification q) +
        dyadicScale (grayCallDepth q e) <= dyadicScale e := by
  have hk := halfAmplification_pos q
  have hcall := (grayCallDepth_scale_bounds q e).2
  have hquarter : dyadicScale e / (24 * halfAmplification q) =
      (1 / 4 : Rat) * (dyadicScale e / (6 * halfAmplification q)) := by
    field_simp [ne_of_gt hk]
    ring
  have hdiv0 : 0 <= dyadicScale e / (6 * halfAmplification q) :=
    div_nonneg (dyadicScale_pos e).le
      (mul_nonneg (by norm_num) hk.le)
  rw [hquarter] at hcall
  linarith

/-- A tail step keeps every frozen son base below `dyadicScale e`. -/
lemma grayTail_all_frozen_base_le_step
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove)
    (hshape : GrayTailShape st)
    (hprev : forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase st.frozen i c <= dyadicScale e)
    (hactive : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase st.frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase
        (grayTailStep q L a e sigma A st sm).frozen i c <= dyadicScale e := by
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hprev
  · split
    · exact hprev
    · split
      · have happ : forall (i : Fin n) (c : Fin b),
            grayTailFrozenSonBase
              (st.frozen ++
                [{ serverTime := st.time
                   roundIndex := st.frozen.length
                   epsDepth := grayTailRoundEps q L e st.frozen.length
                   slots := st.slots
                   move := grayTailCurrentMove q L e sigma st
                   allocated := grayTailLocalAllocatedList
                     (grayTailLocalServerMove
                       (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
                   unavailable := st.unavailable }]) i c <= dyadicScale e := by
          intro i c
          rw [grayTailFrozenSonBase_append_global]
          by_cases hson : GrayTailHasKey st.slots i c
          · obtain ⟨s, hs, hi, hc⟩ := hson
            have hold : grayTailFrozenSonBase st.frozen i c <=
                dyadicScale e - dyadicScale e /
                  (6 * halfAmplification q) := by
              simpa [hi, hc] using hactive s hs
            have hnew := grayTailRoundSonBase_le_callScale_of_goal
              (n := n) (b := b) (q := q) (L := L) (e := e)
              (r := st.frozen.length) (A := st.unavailable)
              (slots := st.slots) (move := grayTailCurrentMove q L e sigma st)
              (server := grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
              (by assumption) hshape.slots_nodup hshape.slots_round i c
            exact le_trans (add_le_add hold hnew)
              (grayTail_callScale_add_threshold_le q e)
          · rw [grayTailSonBase_eq_zero_of_not_hasKey i c hson, add_zero]
            exact hprev i c
        exact happ
      · exact hprev
/-- At every time of a tail run, every frozen son base is at most `dyadicScale e`. -/
theorem grayTail_all_frozen_base_le_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen i c <= dyadicScale e := by
  induction t with
  | zero =>
      intro i c
      simp [grayTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase, (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayTailStateAt_succ]
      apply grayTail_all_frozen_base_le_step q L a e sigma A _ (sm t)
        (grayTailShape_stateAt q L a e sigma A sm t) ih
      exact grayTail_active_base_le_stateAt_global q L a e sigma A sm t

/-- At most `used` children of a client are below `used`. -/
lemma grayTail_source_fin_card_le (b used : Nat) :
    (Finset.univ.filter (fun c : Fin b => c.val < used)).card <= used := by
  have hsub : (Finset.univ.filter (fun c : Fin b => c.val < used)).card <=
      (Finset.range used).card := by
    refine Finset.card_le_card_of_injOn (fun c => c.val) ?_ ?_
    · intro c hc
      have hc' : c ∈ Finset.univ.filter
          (fun c : Fin b => c.val < used) := hc
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hc').2
    · intro c _ d _ h
      exact Fin.ext h
  simpa using hsub

/-- The total frozen request of a tail run never exceeds `n * 2 ^ (e - a)` times
`dyadicScale e`. -/
theorem grayTailFrozenRequestSum_le_source_budget
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    grayTailFrozenRequestSum
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
  rw [← grayTailFrozenSourceBaseSum_eq_requestSum]
  unfold grayTailFrozenSourceBaseSum
  have hinner : forall i : Fin n,
      (∑ c : Fin b,
        if c.val < 2 ^ (e - a) then
          grayTailFrozenSonBase
            (grayTailStateAt (n := n) (b := b)
              q L a e sigma A sm t).frozen i c else 0) <=
        ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
    intro i
    calc
      (∑ c : Fin b,
          if c.val < 2 ^ (e - a) then
            grayTailFrozenSonBase
              (grayTailStateAt (n := n) (b := b)
                q L a e sigma A sm t).frozen i c else 0) =
          ∑ c ∈ Finset.univ.filter
            (fun c : Fin b => c.val < 2 ^ (e - a)),
              grayTailFrozenSonBase
                (grayTailStateAt (n := n) (b := b)
                  q L a e sigma A sm t).frozen i c := by
            rw [Finset.sum_filter]
      _ <= ∑ _c ∈ Finset.univ.filter
            (fun c : Fin b => c.val < 2 ^ (e - a)),
              dyadicScale e := by
            apply Finset.sum_le_sum
            intro c hc
            exact grayTail_all_frozen_base_le_stateAt
              q L a e sigma A sm t i c
      _ = ((Finset.univ.filter
            (fun c : Fin b => c.val < 2 ^ (e - a))).card : Rat) *
              dyadicScale e := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
            apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
            exact_mod_cast grayTail_source_fin_card_le b (2 ^ (e - a))
  calc
    (∑ i : Fin n, ∑ c : Fin b,
        if c.val < 2 ^ (e - a) then
          grayTailFrozenSonBase
            (grayTailStateAt (n := n) (b := b)
              q L a e sigma A sm t).frozen i c else 0) <=
        ∑ _i : Fin n,
          ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
            apply Finset.sum_le_sum
            intro i _
            exact hinner i
    _ = ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_fin]
          push_cast
          ring

/-- The SUV global-width invariant (p. 143): every frozen round after the
first was selected by a failed global stop test, so it carries more than a
quarter of all source sons; and while the controller is not terminal, the
current slot list is either the initial full family or itself wider than a
quarter.  This is what makes the round budget independent of the family
size. -/
structure GrayTailWidthInvariant {n b : Nat} (sourceCount : Nat)
    (st : GrayTailState n b) : Prop where
  current : st.frozen = [] ∨ st.done = true ∨
    sourceCount < 4 * st.slots.length
  frozenTail : forall p, p ∈ st.frozen.tail ->
    sourceCount < 4 * p.slots.length

/-- The initial tail state satisfies the width invariant. -/
lemma grayTailWidthInvariant_initial (n b a e : Nat) (A : Allocation) :
    GrayTailWidthInvariant (n * 2 ^ (e - a))
      (grayTailInitialState n b a e A) := by
  constructor
  · left
    rfl
  · simp [grayTailInitialState]

/-- Freezing a round preserves the width invariant, provided the run finishes or keeps more than
a quarter of the slab open. -/
lemma grayTailWidthInvariant_freeze {n b sourceCount : Nat}
    {st : GrayTailState n b} (hst : GrayTailWidthInvariant sourceCount st)
    (hactive : ¬(st.done || st.slots.isEmpty) = true)
    (p : GrayTailRound n b)
    (hpSlots : p.slots = st.slots) (next : List (GrayTailSlot n b))
    (time roundStart : Nat) (done : Bool)
    (hnext : done = true ∨ sourceCount < 4 * next.length)
    (unavailable : Allocation)
    (anchoringSlots : List (GrayTailSlot n b))
    (history : FamilyGameHistory) :
    GrayTailWidthInvariant sourceCount
      ({ time := time
         roundStart := roundStart
         done := done
         frozen := st.frozen ++ [p]
         unavailable := unavailable
         slots := next
         anchoringSlots := anchoringSlots
         history := history } : GrayTailState n b) := by
  constructor
  · right
    exact hnext
  · intro r hr
    cases hfrozen : st.frozen with
    | nil =>
        simp [hfrozen] at hr
    | cons first rest =>
        have hr' : r ∈ rest ++ [p] := by
          simpa [hfrozen] using hr
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact hst.frozenTail r (by simpa [hfrozen] using hr')
        · have hrp : r = p := by simpa using hr'
          subst r
          rw [hpSlots]
          rcases hst.current with hempty | hslots
          · simp [hfrozen] at hempty
          · rcases hslots with hdone | hwide
            · have : (st.done || st.slots.isEmpty) = true := by
                simp [hdone]
              exact (hactive this).elim
            · exact hwide

/-- Either the global quarter test fires, or more than a quarter of the slab is still open. -/
lemma grayTail_global_stopped_width {n b : Nat} (used : Nat)
    (slots : List (GrayTailSlot n b)) (cap : Bool) :
    (grayTailGlobalQuarterB (n := n) used slots || cap) = true ∨
      n * used < 4 * slots.length := by
  by_cases hstop : 4 * slots.length <= n * used
  · left
    simp [grayTailGlobalQuarterB, hstop]
  · right
    omega

/-- A tail step preserves the width invariant `n * 2 ^ (e - a)`. -/
lemma grayTailWidthInvariant_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailWidthInvariant (n * 2 ^ (e - a)) st) :
    GrayTailWidthInvariant (n * 2 ^ (e - a))
      (grayTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · simp [grayTailWaitingB] at hw
  · by_cases hd : st.done = true
    · simp only [grayTailStep, Bool.false_eq_true, hw, hd, ↓reduceIte]
      exact ⟨Or.inr (Or.inl rfl), hst.frozenTail⟩
    · by_cases hs : st.slots.isEmpty = true
      · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, ↓reduceIte]
        rcases hst.current with h | h | h
        · exact ⟨Or.inl h, hst.frozenTail⟩
        · exact absurd h hd
        · exact ⟨Or.inr (Or.inr h), hst.frozenTail⟩
      · by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg,
            ↓reduceIte]
          exact grayTailWidthInvariant_freeze hst (by simp [hd, hs]) _ rfl
            _ _ _ _ (grayTail_global_stopped_width _ _ _) _ _ _
        · simp only [grayTailStep, Bool.false_eq_true, hw, hd, hs, hg,
            ↓reduceIte]
          rcases hst.current with h | h | h
          · exact ⟨Or.inl h, hst.frozenTail⟩
          · exact absurd h hd
          · exact ⟨Or.inr (Or.inr h), hst.frozenTail⟩

/-- Every state of a tail run satisfies the width invariant `n * 2 ^ (e - a)`. -/
theorem grayTailWidthInvariant_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailWidthInvariant (n * 2 ^ (e - a))
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayTailWidthInvariant_initial n b a e A
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailWidthInvariant_step q L a e sigma A _ (sm t) ih

/-- A round meeting the robust gray goal has amplified total root request at least `n * beta`. -/
lemma grayTailRobustGoal_totalRequest_lower
    {kappa beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {move : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : familyRobustGrayGoalAtB kappa beta epsDepth deltaDepth n
      A move server = true) :
    (n : Rat) * beta <= kappa * totalRootRequest n move := by
  have hweak := familyRobustGrayGoalAtB.to_familyGrayGoalAtB hgoal
  unfold familyGrayGoalAtB at hweak
  rw [Bool.and_eq_true] at hweak
  have hthird : decide ((n : Rat) * beta <=
      kappa * totalRootRequest n move) = true := hweak.2
  exact of_decide_eq_true hthird

/-- If every frozen round contributes at least `g` after amplification, the frozen request sum
grows linearly in the number of rounds. -/
lemma grayTailFrozenRequestSum_lower_of_each {n b : Nat}
    (frozen : GrayTailFrozen n b) (kappa g : Rat)
    (h : forall p, p ∈ frozen ->
      g <= kappa * totalRootRequest p.slots.length p.move) :
    (frozen.length : Rat) * g <=
      kappa * grayTailFrozenRequestSum frozen := by
  induction frozen with
  | nil => simp [grayTailFrozenRequestSum]
  | cons p frozen ih =>
      have hp := h p (by simp)
      have hrest : forall r, r ∈ frozen ->
          g <= kappa * totalRootRequest r.slots.length r.move := by
        intro r hr
        exact h r (by simp [hr])
      have hi := ih hrest
      unfold grayTailFrozenRequestSum
      simp only [List.foldr_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      calc
        (↑frozen.length + 1) * g = g + ↑frozen.length * g := by ring
        _ <= kappa * totalRootRequest p.slots.length p.move +
            kappa * List.foldr
              (fun p acc => totalRootRequest p.slots.length p.move + acc)
              0 frozen := add_le_add hp hi
        _ = kappa *
            (totalRootRequest p.slots.length p.move +
              List.foldr
                (fun p acc => totalRootRequest p.slots.length p.move + acc)
                0 frozen) := by ring

/-- Every frozen round after the first carries more than a quarter of the
source family, so the accumulated request grows linearly in the number of
rounds -- the SUV width-budget lower bound. -/
theorem grayTailFrozenTailRequestSum_lower
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    let st := grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t
    ((st.frozen.tail.length : Nat) : Rat) *
        (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) <=
      halfAmplification q * grayTailFrozenRequestSum st.frozen.tail := by
  dsimp only
  apply grayTailFrozenRequestSum_lower_of_each
  intro p hp
  have hwide := (grayTailWidthInvariant_stateAt
    q L a e sigma A sm t).frozenTail p hp
  have hwideRat : ((n * 2 ^ (e - a) : Nat) : Rat) <
      4 * (p.slots.length : Rat) := by
    exact_mod_cast hwide
  have hvalid := (grayTailCertified_stateAt
    q L a e sigma A sm t).round_valid p
      (List.mem_of_mem_tail hp)
  have hreq := grayTailRobustGoal_totalRequest_lower hvalid.2.2.2.2.1
  have hbeta : 0 < (3 / 4 : Rat) *
      dyadicScale (grayCallDepth q e) :=
    mul_pos (by norm_num) (dyadicScale_pos _)
  have hscaled : (((n * 2 ^ (e - a) : Nat) : Rat) / 4) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <
      (p.slots.length : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) := by
    apply mul_lt_mul_of_pos_right _ hbeta
    linarith
  exact le_trans hscaled.le hreq

/-- The tail round count is chosen so large that the linear growth of the frozen request cannot
fit under the amplified budget `halfAmplification q * dyadicScale e`. -/
lemma grayTail_roundCount_tail_progress_contradiction (q e : Nat)
    (hprogress : (((grayTailRoundCount q - 1 : Nat) : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 <=
      halfAmplification q * dyadicScale e)) : False := by
  let d : Nat := 24 * q + 40
  have heps : (0 : Rat) < dyadicScale e := dyadicScale_pos e
  have hdpos : (0 : Rat) < (d : Nat) := by
    dsimp only [d]
    positivity
  have hpowNat : 2 ^ (Nat.size (3 * q + 5) + 2) <= d := by
    rw [show Nat.size (3 * q + 5) + 2 =
      (Nat.size (3 * q + 5) + 1) + 1 by omega, pow_succ, pow_succ]
    have h := two_pow_size_upper q
    dsimp only [d]
    omega
  have hpow : (2 : Rat) ^ (Nat.size (3 * q + 5) + 2) <=
      (d : Nat) := by
    exact_mod_cast hpowNat
  have hscale : dyadicScale e / (d : Nat) <=
      dyadicScale (grayCallDepth q e) := by
    rw [grayCallDepth, dyadicScale_add]
    exact div_le_div_of_nonneg_left heps.le (by positivity) hpow
  have hroundPos : 1 <= grayTailRoundCount q := by
    unfold grayTailRoundCount
    have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
    omega
  have hroundCast : (((grayTailRoundCount q - 1 : Nat) : Rat)) =
      256 * (((q : Nat) : Rat) + 1) ^ 2 - 1 := by
    rw [Nat.cast_sub hroundPos]
    norm_num [grayTailRoundCount]
  have hcoef : halfAmplification q <
      (((grayTailRoundCount q - 1 : Nat) : Rat) * (3 / 4 : Rat) / 4) /
        (d : Nat) := by
    rw [hroundCast]
    simp only [halfAmplification, d]
    push_cast
    rw [lt_div_iff₀ (by positivity : (0 : Rat) < 24 * (q : Rat) + 40)]
    have hq : (0 : Rat) <= (q : Nat) := by positivity
    nlinarith
  have hcoefEps := mul_lt_mul_of_pos_right hcoef heps
  have hfactor0 : (0 : Rat) <=
      ((grayTailRoundCount q - 1 : Nat) : Rat) * (3 / 4 : Rat) / 4 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hscale hfactor0
  have hstrict : halfAmplification q * dyadicScale e <
      ((grayTailRoundCount q - 1 : Nat) : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 := by
    calc
      halfAmplification q * dyadicScale e <
          ((((grayTailRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) / (d : Nat)) * dyadicScale e := hcoefEps
      _ = (((grayTailRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) * (dyadicScale e / (d : Nat)) := by ring
      _ <= (((grayTailRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) *
            dyadicScale (grayCallDepth q e) := hscaled
      _ = ((grayTailRoundCount q - 1 : Nat) : Rat) *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 := by ring
  exact (not_lt_of_ge hprogress) hstrict

/-- A sum of nonnegative root requests is nonnegative. -/
lemma grayTailEntryRequestSum_nonneg {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove))
    (h : forall z, z ∈ entries -> 0 <= getReq z.2 []) :
    0 <= grayTailEntryRequestSum entries := by
  induction entries with
  | nil => simp [grayTailEntryRequestSum]
  | cons z entries ih =>
      unfold grayTailEntryRequestSum
      simp only [List.foldr_cons]
      exact add_nonneg (h z (by simp))
        (ih (fun w hw => h w (by simp [hw])))

/-- Dropping the first frozen round does not increase the frozen request sum. -/
lemma grayTailFrozenRequestSum_tail_le {n b : Nat}
    (frozen : GrayTailFrozen n b)
    (h : forall p, p ∈ frozen ->
      0 <= totalRootRequest p.slots.length p.move) :
    grayTailFrozenRequestSum frozen.tail <=
      grayTailFrozenRequestSum frozen := by
  cases frozen with
  | nil => simp [grayTailFrozenRequestSum]
  | cons p frozen =>
      unfold grayTailFrozenRequestSum
      simp only [List.tail_cons, List.foldr_cons]
      exact le_add_of_nonneg_left (h p (by simp))

/-- Once the tail round budget is spent, a tail run has no open slots left. -/
theorem grayTail_slots_eq_nil_of_roundCount_stateAt_global
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hcount : grayTailRoundCount q <=
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.length) :
    (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).slots = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact Fin.elim0 s.1
  have hsourceNat : 0 < n * 2 ^ (e - a) :=
    Nat.mul_pos hn (by positivity)
  have hsource : (0 : Rat) < ((n * 2 ^ (e - a) : Nat) : Rat) := by
    exact_mod_cast hsourceNat
  have hroundNonneg : forall p,
      p ∈ (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen ->
      0 <= totalRootRequest p.slots.length p.move := by
    intro p hp
    have hvalid := (grayTailCertified_stateAt
      q L a e sigma A sm t).round_valid p hp
    have hpoint := familyRobustGrayGoalAtB.to_pointwise
      hvalid.2.2.2.2.1
    rw [totalRootRequest_eq_grayTailEntryRequestSum]
    apply grayTailEntryRequestSum_nonneg
    exact grayTailSlotEntries_root_nonneg_global
      (halfAmplification_pos q)
      (mul_nonneg (by norm_num) (dyadicScale_pos _).le) hpoint
  have htailAll := grayTailFrozenRequestSum_tail_le
    (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).frozen hroundNonneg
  have hupper := grayTailFrozenRequestSum_le_source_budget
    (n := n) (b := b) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have htailUpper : grayTailFrozenRequestSum
        (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen.tail <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e :=
    le_trans htailAll hupper
  have hlower := grayTailFrozenTailRequestSum_lower
    (n := n) (b := b) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have hkpos := halfAmplification_pos q
  have hlowerUpper := le_trans hlower
    (mul_le_mul_of_nonneg_left htailUpper hkpos.le)
  have hroundPos : 1 <= grayTailRoundCount q := by
    unfold grayTailRoundCount
    have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
    omega
  have htailCount : grayTailRoundCount q - 1 <=
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.tail.length := by
    rw [List.length_tail]
    omega
  have htailCountRat : ((grayTailRoundCount q - 1 : Nat) : Rat) <=
      (((grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.tail.length : Nat) : Rat) := by
    exact_mod_cast htailCount
  have hfactor0 : (0 : Rat) <=
      (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) := by
    exact mul_nonneg (div_nonneg hsource.le (by norm_num))
      (mul_nonneg (by norm_num) (dyadicScale_pos _).le)
  have hcountScaled := mul_le_mul_of_nonneg_right htailCountRat hfactor0
  have hmain := le_trans hcountScaled hlowerUpper
  have hmain' : ((n * 2 ^ (e - a) : Nat) : Rat) *
        (((grayTailRoundCount q - 1 : Nat) : Rat) *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4) <=
      ((n * 2 ^ (e - a) : Nat) : Rat) *
        (halfAmplification q * dyadicScale e) := by
    calc
      ((n * 2 ^ (e - a) : Nat) : Rat) *
          (((grayTailRoundCount q - 1 : Nat) : Rat) *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4) =
        ((grayTailRoundCount q - 1 : Nat) : Rat) *
          (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) := by ring
      _ <= halfAmplification q *
          (((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e) := hmain
      _ = ((n * 2 ^ (e - a) : Nat) : Rat) *
          (halfAmplification q * dyadicScale e) := by ring
  have hcancel : ((grayTailRoundCount q - 1 : Nat) : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 <=
      halfAmplification q * dyadicScale e := by
    nlinarith [hmain']
  exact grayTail_roundCount_tail_progress_contradiction q e hcancel

end Kolmogorov
