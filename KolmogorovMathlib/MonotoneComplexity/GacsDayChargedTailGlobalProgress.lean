import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailBounds
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.SourceInvariant
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.Certification
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay

/-!
# Global progress for the designated-charge tail

The charged controller has the same source budget and quarter-width stopping
rule as the robust tail.  Its accepted rounds carry the request window in the
finite designated-charge witness instead of `familyPointwiseGrayAtB`.  This
file repeats only the controller-dependent part of the global argument.
-/

namespace Kolmogorov

open scoped BigOperators

/-- Every state of a charged tail run only uses the first `grayChargedSourceCount a e` children. -/
theorem grayChargedTailSourceInvariant_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailSourceInvariant (grayChargedSourceCount a e)
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedSourceInvariant_initial n b a e A
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedSourceInvariant_step q L a e sigma A _ (sm t) ih

/-- A round meeting the charged tail goal requests, at each client root, between half and all of
`dyadicScale (grayCallDepth q e)`. -/
lemma grayChargedTailGoalAtB_root_bounds
    {q e epsDepth deltaDepth n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedTailGoalAtB q e epsDepth deltaDepth n A move server = true)
    (j : Fin n) :
    dyadicScale (grayCallDepth q e) / 2 <=
        getFamilyReq move j.val [] ∧
      getFamilyReq move j.val [] <= dyadicScale (grayCallDepth q e) := by
  unfold grayChargedTailGoalAtB at hgoal
  obtain ⟨G, _hGmem, hG⟩ :=
    familyChargedGrayGoalAtB.exists_charge hgoal
  have hj := familyGrayChargeAtB.root hG j.isLt
  exact ⟨hj.1, hj.2.1⟩

/-- A round meeting the spend goal requests, at each client root, between half and all of
`dyadicScale (grayChargedSpendAlphaDepth a)`. -/
lemma grayChargedSpendGoalAtB_root_bounds
    {q L a e pass n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedSpendGoalAtB q L a e pass n A move server = true)
    (j : Fin n) :
    dyadicScale (grayChargedSpendAlphaDepth a) / 2 <=
        getFamilyReq move j.val [] ∧
      getFamilyReq move j.val [] <=
        dyadicScale (grayChargedSpendAlphaDepth a) := by
  unfold grayChargedSpendGoalAtB at hgoal
  obtain ⟨G, _hGmem, hG⟩ :=
    familyChargedGrayGoalAtB.exists_charge hgoal
  have hj := familyGrayChargeAtB.root hG j.isLt
  exact ⟨hj.1, hj.2.1⟩

/-- In a round meeting the charged tail goal, whose slots all sit in the same round, no son base
exceeds `dyadicScale (grayCallDepth q e)`. -/
lemma grayChargedRoundSonBase_le_callScale_of_goal
    {n b q e epsDepth deltaDepth r : Nat} {A : Allocation}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : grayChargedTailGoalAtB q e epsDepth deltaDepth
      slots.length A move server = true)
    (hnodup : slots.Nodup)
    (hround : forall s, s ∈ slots -> s.2.2.val = r)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c <=
      dyadicScale (grayCallDepth q e) := by
  apply grayTailSonBase_le_of_slot_request_bounds
    (dyadicScale_pos _).le hnodup hround
  · intro j
    have hj := (grayChargedTailGoalAtB_root_bounds hgoal j).1
    have hscale : 0 <= dyadicScale (grayCallDepth q e) / 2 := by
      exact div_nonneg (dyadicScale_pos _).le (by norm_num)
    exact le_trans hscale hj
  · intro j
    exact (grayChargedTailGoalAtB_root_bounds hgoal j).2

/-- A tail step keeps every open slot below the service threshold
`dyadicScale e - dyadicScale e / (6 * halfAmplification q)`. -/
lemma grayChargedTail_active_base_le_step
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailState n b) (sm : FamilyServerMove)
    (hprev : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase st.frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall s, s ∈ (grayChargedTailStep q L a e sigma A st sm).slots ->
      grayTailFrozenSonBase
          (grayChargedTailStep q L a e sigma A st sm).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  unfold grayChargedTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hprev
  · split
    · exact hprev
    · split
      · intro s hs
        exact grayTailNextSlots_base_le_global hs
      · exact hprev

/-- At every time of a charged tail run, every open slot is below the service threshold. -/
theorem grayChargedTail_active_base_le_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall s, s ∈ (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots ->
      grayTailFrozenSonBase
          (grayChargedTailStateAt (n := n) (b := b)
            q L a e sigma A sm t).frozen s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  induction t with
  | zero =>
      intro s hs
      simpa [grayChargedTailStateAt, grayChargedTailFold,
        grayChargedTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase] using
        grayTail_threshold_nonneg_global q e
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTail_active_base_le_step q L a e sigma A _ (sm t) ih

/-- A tail step keeps every frozen son base below `dyadicScale e`. -/
lemma grayChargedTail_all_frozen_base_le_step
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
        (grayChargedTailStep q L a e sigma A st sm).frozen i c <=
          dyadicScale e := by
  unfold grayChargedTailStep
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
            have hnew := grayChargedRoundSonBase_le_callScale_of_goal
              (n := n) (b := b) (q := q) (e := e)
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

/-- At every time of a charged tail run, every frozen son base is at most `dyadicScale e`. -/
theorem grayChargedTail_all_frozen_base_le_stateAt
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall (i : Fin n) (c : Fin b),
      grayTailFrozenSonBase
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen i c <= dyadicScale e := by
  induction t with
  | zero =>
      intro i c
      simp [grayChargedTailStateAt, grayChargedTailFold,
        grayChargedTailInitialState, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase, (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      apply grayChargedTail_all_frozen_base_le_step q L a e sigma A _ (sm t)
        (grayChargedTailShape_stateAt q L a e sigma A sm t) ih
      exact grayChargedTail_active_base_le_stateAt q L a e sigma A sm t

/-- Every frozen entry of a charged tail run sits at one of the `2 ^ (e - a)` used children. -/
lemma grayChargedTailFrozenEntries_used
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat}
    {z : GrayTailSlot n b × ClientMove}
    (hz : z ∈ grayTailFrozenEntries
      (grayChargedTailStateAt q L a e sigma A sm t).frozen) :
    z.1.2.1.val < 2 ^ (e - a) := by
  unfold grayTailFrozenEntries at hz
  rw [List.mem_flatMap] at hz
  obtain ⟨p, hp, hz⟩ := hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hsource := grayChargedTailSourceInvariant_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  exact hsource.frozen p hp (p.slots.get j) (List.get_mem p.slots j)

/-- For a charged tail run, summing the frozen son bases over the used children gives the total
frozen request. -/
lemma grayChargedTailFrozenSourceBaseSum_eq_requestSum
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    grayTailFrozenSourceBaseSum (2 ^ (e - a))
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen =
      grayTailFrozenRequestSum
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen := by
  rw [grayTailFrozenRequestSum_eq_entries]
  unfold grayTailFrozenSourceBaseSum grayTailFrozenSonBase
  apply grayTailSourceBaseSum_eq_entryRequestSum
  intro z hz
  exact grayChargedTailFrozenEntries_used hz

/-- The total frozen request of a charged tail run never exceeds the source budget
`n * 2 ^ (e - a)` times `dyadicScale e`. -/
theorem grayChargedTailFrozenRequestSum_le_source_budget
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    grayTailFrozenRequestSum
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
  rw [← grayChargedTailFrozenSourceBaseSum_eq_requestSum]
  unfold grayTailFrozenSourceBaseSum
  have hinner : forall i : Fin n,
      (∑ c : Fin b,
        if c.val < 2 ^ (e - a) then
          grayTailFrozenSonBase
            (grayChargedTailStateAt (n := n) (b := b)
              q L a e sigma A sm t).frozen i c else 0) <=
        ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
    intro i
    calc
      (∑ c : Fin b,
          if c.val < 2 ^ (e - a) then
            grayTailFrozenSonBase
              (grayChargedTailStateAt (n := n) (b := b)
                q L a e sigma A sm t).frozen i c else 0) =
          ∑ c ∈ Finset.univ.filter
            (fun c : Fin b => c.val < 2 ^ (e - a)),
              grayTailFrozenSonBase
                (grayChargedTailStateAt (n := n) (b := b)
                  q L a e sigma A sm t).frozen i c := by
            rw [Finset.sum_filter]
      _ <= ∑ _c ∈ Finset.univ.filter
            (fun c : Fin b => c.val < 2 ^ (e - a)),
              dyadicScale e := by
            apply Finset.sum_le_sum
            intro c hc
            exact grayChargedTail_all_frozen_base_le_stateAt
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
            (grayChargedTailStateAt (n := n) (b := b)
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

/-- A charged tail step preserves the width invariant: at most `n * 2 ^ (e - a)` slots stay open. -/
lemma grayChargedTailWidthInvariant_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hst : GrayTailWidthInvariant (n * 2 ^ (e - a)) st) :
    GrayTailWidthInvariant (n * 2 ^ (e - a))
      (grayChargedTailStep q L a e sigma A st sm) := by
  by_cases hw : grayTailWaitingB st = true
  · simp [grayTailWaitingB] at hw
  · by_cases hd : st.done = true
    · simp only [grayChargedTailStep, Bool.false_eq_true, hw, hd,
        ↓reduceIte]
      exact ⟨Or.inr (Or.inl rfl), hst.frozenTail⟩
    · by_cases hs : st.slots.isEmpty = true
      · simp only [grayChargedTailStep, Bool.false_eq_true, hw, hd, hs,
          ↓reduceIte]
        rcases hst.current with h | h | h
        · exact ⟨Or.inl h, hst.frozenTail⟩
        · exact absurd h hd
        · exact ⟨Or.inr (Or.inr h), hst.frozenTail⟩
      · by_cases hg : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true
        · simp only [grayChargedTailStep, Bool.false_eq_true, hw, hd, hs,
            hg, ↓reduceIte]
          exact grayTailWidthInvariant_freeze hst (by simp [hd, hs]) _ rfl
            _ _ _ _ (grayTail_global_stopped_width _ _ _) _ _ _
        · simp only [grayChargedTailStep, Bool.false_eq_true, hw, hd, hs,
            hg, ↓reduceIte]
          rcases hst.current with h | h | h
          · exact ⟨Or.inl h, hst.frozenTail⟩
          · exact absurd h hd
          · exact ⟨Or.inr (Or.inr h), hst.frozenTail⟩

/-- Every state of a charged tail run satisfies the width invariant `n * 2 ^ (e - a)`. -/
theorem grayChargedTailWidthInvariant_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailWidthInvariant (n * 2 ^ (e - a))
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      simpa [grayChargedTailStateAt, grayChargedTailFold,
        grayChargedTailInitialState, grayTailInitialState,
        grayChargedSourceCount] using
        grayTailWidthInvariant_initial n b a e A
  | succ t ih =>
      rw [grayChargedTailStateAt_succ]
      exact grayChargedTailWidthInvariant_step q L a e sigma A _ (sm t) ih

/-- A round meeting the charged tail goal has amplified total root request at least three
quarters of `dyadicScale (grayCallDepth q e)` per slot. -/
lemma grayChargedTailGoal_totalRequest_lower
    {q e epsDepth deltaDepth n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedTailGoalAtB q e epsDepth deltaDepth n
      A move server = true) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <=
      halfAmplification q * totalRootRequest n move := by
  unfold grayChargedTailGoalAtB at hgoal
  have hweak := familyChargedGrayGoalAtB.to_familyGrayGoalAtB hgoal
  unfold familyGrayGoalAtB at hweak
  rw [Bool.and_eq_true] at hweak
  exact of_decide_eq_true hweak.2

/-- In a round meeting the charged tail goal, every slot entry requests a nonnegative amount at
the root. -/
lemma grayChargedTailSlotEntries_root_nonneg
    {n b q e epsDepth deltaDepth : Nat} {A : Allocation}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : grayChargedTailGoalAtB q e epsDepth deltaDepth
      slots.length A move server = true) :
    forall z, z ∈ grayTailSlotEntries slots move -> 0 <= getReq z.2 [] := by
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hj := (grayChargedTailGoalAtB_root_bounds hgoal j).1
  unfold getFamilyReq at hj
  have hscale : 0 <= dyadicScale (grayCallDepth q e) / 2 :=
    div_nonneg (dyadicScale_pos _).le (by norm_num)
  exact le_trans hscale hj

/-- Every frozen round after the first contributes at least a quarter of the source slab at three
quarters of the call scale, so the amplified frozen request grows linearly in the number of
rounds. -/
theorem grayChargedTailFrozenTailRequestSum_lower
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat} :
    let st := grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t
    ((st.frozen.tail.length : Nat) : Rat) *
        (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) <=
      halfAmplification q * grayTailFrozenRequestSum st.frozen.tail := by
  dsimp only
  apply grayTailFrozenRequestSum_lower_of_each
  intro p hp
  have hwide := (grayChargedTailWidthInvariant_stateAt
    q L a e sigma A sm t).frozenTail p hp
  have hwideRat : ((n * 2 ^ (e - a) : Nat) : Rat) <
      4 * (p.slots.length : Rat) := by
    exact_mod_cast hwide
  have hvalid := (grayChargedTailCertified_stateAt
    q L a e sigma A sm t).round_valid p
      (List.mem_of_mem_tail hp)
  have hreq := grayChargedTailGoal_totalRequest_lower hvalid.2.2.2.2.1
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

/-- The advantage round budget is chosen so large that the linear growth of the frozen request
cannot fit under the amplified budget `halfAmplification q * dyadicScale e`. -/
lemma grayCharged_roundCount_tail_progress_contradiction (q e : Nat)
    (hprogress : (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
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
  have hroundPos : 1 <= grayChargedAdvantageRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq]
    have hq : 0 < (q + 1) ^ 2 := by positivity
    omega
  have hroundCast :
      (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat)) =
        256 * (((q : Nat) : Rat) + 1) ^ 2 - 9 := by
    have hqpos : 0 < (q + 1) ^ 2 := by positivity
    have hqSq : 1 <= (q + 1) ^ 2 := hqpos
    have hlarge : 256 <= 256 * (q + 1) ^ 2 := by
      simpa using Nat.mul_le_mul_left 256 hqSq
    have hfour : 8 <= 256 * (q + 1) ^ 2 :=
      le_trans (by norm_num : 8 <= 256) hlarge
    rw [Nat.cast_sub hroundPos, grayChargedAdvantageRoundCount_eq,
      Nat.cast_sub hfour]
    push_cast
    ring
  have hcoef : halfAmplification q <
      (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
        (3 / 4 : Rat) / 4) / (d : Nat) := by
    rw [hroundCast]
    simp only [halfAmplification, d]
    push_cast
    rw [lt_div_iff₀ (by positivity : (0 : Rat) < 24 * (q : Rat) + 40)]
    have hq : (0 : Rat) <= (q : Nat) := by positivity
    nlinarith
  have hcoefEps := mul_lt_mul_of_pos_right hcoef heps
  have hfactor0 : (0 : Rat) <=
      ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
        (3 / 4 : Rat) / 4 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hscale hfactor0
  have hstrict : halfAmplification q * dyadicScale e <
      ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 := by
    calc
      halfAmplification q * dyadicScale e <
          ((((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) / (d : Nat)) * dyadicScale e := hcoefEps
      _ = (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) * (dyadicScale e / (d : Nat)) := by ring
      _ <= (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
              (3 / 4 : Rat) / 4) *
            dyadicScale (grayCallDepth q e) := hscaled
      _ = ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 := by ring
  exact (not_lt_of_ge hprogress) hstrict

/-- Once the advantage round budget is spent, a charged tail run has no open slots left. -/
theorem grayChargedTail_slots_eq_nil_of_roundCount_stateAt_global
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hcount : grayChargedAdvantageRoundCount q <=
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.length) :
    (grayChargedTailStateAt (n := n) (b := b)
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
      p ∈ (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen ->
      0 <= totalRootRequest p.slots.length p.move := by
    intro p hp
    have hvalid := (grayChargedTailCertified_stateAt
      q L a e sigma A sm t).round_valid p hp
    rw [totalRootRequest_eq_grayTailEntryRequestSum]
    apply grayTailEntryRequestSum_nonneg
    exact grayChargedTailSlotEntries_root_nonneg hvalid.2.2.2.2.1
  have htailAll := grayTailFrozenRequestSum_tail_le
    (grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).frozen hroundNonneg
  have hupper := grayChargedTailFrozenRequestSum_le_source_budget
    (n := n) (b := b) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have htailUpper : grayTailFrozenRequestSum
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).frozen.tail <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e :=
    le_trans htailAll hupper
  have hlower := grayChargedTailFrozenTailRequestSum_lower
    (n := n) (b := b) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have hkpos := halfAmplification_pos q
  have hlowerUpper := le_trans hlower
    (mul_le_mul_of_nonneg_left htailUpper hkpos.le)
  have hroundPos : 1 <= grayChargedAdvantageRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq]
    have hq : 0 < (q + 1) ^ 2 := by positivity
    omega
  have htailCount : grayChargedAdvantageRoundCount q - 1 <=
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.tail.length := by
    rw [List.length_tail]
    omega
  have htailCountRat :
      ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) <=
      (((grayChargedTailStateAt (n := n) (b := b)
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
        (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4) <=
      ((n * 2 ^ (e - a) : Nat) : Rat) *
        (halfAmplification q * dyadicScale e) := by
    calc
      ((n * 2 ^ (e - a) : Nat) : Rat) *
          (((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4) =
        ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
          (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
            ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) := by ring
      _ <= halfAmplification q *
          (((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e) := hmain
      _ = ((n * 2 ^ (e - a) : Nat) : Rat) *
          (halfAmplification q * dyadicScale e) := by ring
  have hcancel : ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) / 4 <=
      halfAmplification q * dyadicScale e := by
    nlinarith [hmain']
  exact grayCharged_roundCount_tail_progress_contradiction q e hcancel

end Kolmogorov
