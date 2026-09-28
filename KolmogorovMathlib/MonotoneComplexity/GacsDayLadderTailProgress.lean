import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailGlobalProgress

/-!
# Quantitative progress in Day's ladder tail

The executable controller stores every completed recursive call.  This file
turns that list into the elementary additive invariant used to rule out the
round-cap branch while an outer son is still active.
-/

namespace Kolmogorov

/-- A retained slot comes from a currently open slot with the same client and child. -/
lemma grayTailRetainedSlots_sourceIndex {n b : Nat}
    {current candidates : List (GrayTailSlot n b)}
    {s : GrayTailSlot n b}
    (hs : s ∈ grayTailRetainedSlots current candidates) :
    ∃ j : Fin current.length,
      (current.get j).1 = s.1 ∧ (current.get j).2.1 = s.2.1 := by
  unfold grayTailRetainedSlots at hs
  have hany := (List.mem_filter.mp hs).2
  rw [List.any_eq_true] at hany
  obtain ⟨old, hold, heq⟩ := hany
  obtain ⟨j, hj⟩ := List.get_of_mem hold
  have hsame : s.1 = old.1 ∧ s.2.1 = old.2.1 := by
    simpa only [grayTailSameSonB, decide_eq_true_eq] using heq
  refine ⟨j, ?_, ?_⟩
  · rw [hj]
    exact hsame.1.symm
  · rw [hj]
    exact hsame.2.symm

/-- In a round meeting the pointwise gray goal, every slot entry requests a nonnegative amount at
the root. -/
lemma grayTailSlotEntries_root_nonneg {n b : Nat}
    {kappa beta : Rat} {epsDepth deltaDepth : Nat}
    {A : Allocation} {slots : List (GrayTailSlot n b)}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hk : 0 < kappa) (hbeta : 0 ≤ beta)
    (hpoint : familyPointwiseGrayAtB kappa beta epsDepth deltaDepth
      slots.length A move server = true) :
    ∀ p ∈ grayTailSlotEntries slots move, 0 ≤ getReq p.2 [] := by
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  have hj := (familyPointwiseGrayAtB.component hpoint j.isLt).1
  unfold getFamilyReq at hj
  nlinarith

/-- Freezing one more round that meets the pointwise goal at a child advances the linear lower
bound on that child's frozen son base. -/
lemma grayTailFrozenSonBase_progress_append {n b : Nat}
    {kappa beta : Rat} {epsDepth deltaDepth : Nat}
    {A : Allocation} {frozen : GrayTailFrozen n b}
    {p : GrayTailRound n b} {server : FamilyServerMove}
    (hk : 0 < kappa) (hbeta : 0 ≤ beta)
    (hpoint : familyPointwiseGrayAtB kappa beta epsDepth deltaDepth
      p.slots.length A p.move server = true)
    (j : Fin p.slots.length) (i : Fin n) (c : Fin b)
    (hi : (p.slots.get j).1 = i) (hc : (p.slots.get j).2.1 = c)
    (hprev : (frozen.length : Rat) * beta ≤
      kappa * grayTailFrozenSonBase frozen i c) :
    ((frozen ++ [p]).length : Rat) * beta ≤
      kappa * grayTailFrozenSonBase (frozen ++ [p]) i c := by
  have hnew := grayTailSlotEntries_selected_progress_global hk hbeta hpoint
    j i c hi hc
  rw [grayTailFrozenSonBase_append_global]
  norm_num only [List.length_append, List.length_singleton, Nat.cast_add,
    Nat.cast_one]
  nlinarith

/-- A child carried into the next round has frozen son base at most the threshold. -/
lemma grayTailNextSlots_base_le {n b e used round : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} {s : GrayTailSlot n b}
    (hs : s ∈ grayTailNextSlots e used round threshold A frozen sm) :
    grayTailFrozenSonBase frozen s.1 s.2.1 ≤ threshold := by
  unfold grayTailNextSlots at hs
  split at hs
  next _ =>
    simp only [List.mem_flatMap] at hs
    obtain ⟨i, _hi, hs⟩ := hs
    simp only [List.mem_map] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    have hpred := (List.mem_filter.mp hc).2
    simp only [Bool.and_eq_true] at hpred
    have hnlt : ¬threshold < grayTailFrozenSonBase frozen i c := by
      intro hlt
      have htrue : decide
          (threshold < grayTailFrozenSonBase frozen i c) = true := by
        simp [hlt]
      have hnot := hpred.1.2
      rw [htrue] at hnot
      norm_num at hnot
    exact le_of_not_gt hnlt
  next _ => simp at hs

/-- A child cannot survive all `grayTailRoundCount q` rounds: the mass it would then have
collected exceeds the service threshold. -/
lemma grayTail_roundCount_progress_contradiction
    (q e : Nat) (gamma : Rat)
    (hprogress : (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) ≤
      halfAmplification q * gamma)
    (hcap : gamma ≤ dyadicScale e -
      dyadicScale e / (6 * halfAmplification q)) : False := by
  have hkpos := halfAmplification_pos q
  have heps := dyadicScale_pos e
  have hscale := (grayCallDepth_scale_bounds q e).1
  have hq1nonneg : (0 : Rat) ≤ ((q + 1 : Nat) : Rat) := by positivity
  have hk_le : halfAmplification q ≤ ((q + 1 : Nat) : Rat) := by
    simp only [halfAmplification]
    have hq : (0 : Rat) ≤ (q : Rat) := by positivity
    push_cast
    linarith
  have hk2 : (halfAmplification q) ^ 2 ≤
      (((q + 1 : Nat) : Rat)) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hk_le)
      (add_nonneg hkpos.le hq1nonneg)
    nlinarith
  have hround_cast : ((grayTailRoundCount q : Nat) : Rat) =
      256 * (((q + 1 : Nat) : Rat)) ^ 2 := by
    norm_num [grayTailRoundCount]
  have hround_bound : 64 * (halfAmplification q) ^ 2 ≤
      ((grayTailRoundCount q : Nat) : Rat) := by
    rw [hround_cast]
    nlinarith
  have hround_pos : (0 : Rat) < (grayTailRoundCount q : Nat) := by
    simp only [grayTailRoundCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    positivity
  have hthreshold_lt : dyadicScale e -
      dyadicScale e / (6 * halfAmplification q) < dyadicScale e := by
    have hdiv : (0 : Rat) < dyadicScale e /
        (6 * halfAmplification q) := by positivity
    linarith
  have hgamma_eps : gamma ≤ dyadicScale e :=
    le_trans hcap hthreshold_lt.le
  have hprogress_eps : (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) ≤
      halfAmplification q * dyadicScale e :=
    le_trans hprogress
      (mul_le_mul_of_nonneg_left hgamma_eps hkpos.le)
  have hlower_lt : (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) *
          (dyadicScale e / (48 * halfAmplification q))) <
      (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) := by
    have hm := mul_lt_mul_of_pos_left hscale
      (mul_pos hround_pos (by norm_num : (0 : Rat) < 3 / 4))
    simpa only [mul_assoc] using hm
  have hlower_eq : (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) *
          (dyadicScale e / (48 * halfAmplification q))) =
      ((grayTailRoundCount q : Rat) * dyadicScale e) /
        (64 * halfAmplification q) := by
    (field_simp [ne_of_gt hkpos]; ring)
  have hround_mul := mul_le_mul_of_nonneg_right hround_bound heps.le
  have hbig : halfAmplification q * dyadicScale e ≤
      (grayTailRoundCount q : Rat) *
        ((3 / 4 : Rat) *
          (dyadicScale e / (48 * halfAmplification q))) := by
    rw [hlower_eq, le_div_iff₀ (mul_pos (by norm_num) hkpos)]
    ring_nf at hround_mul ⊢
    exact hround_mul
  exact (not_lt_of_ge hbig) (lt_of_lt_of_le hlower_lt hprogress_eps)

/-- Adding a slot raises the slot count of its own client by one and leaves the others alone. -/
lemma grayTailRootSlotCount_cons {n b : ℕ} (s : GrayTailSlot n b)
    (slots : List (GrayTailSlot n b)) (i : Fin n) :
    grayTailRootSlotCount (s :: slots) i =
      grayTailRootSlotCount slots i + if s.1 = i then 1 else 0 := by
  unfold grayTailRootSlotCount
  simp only [List.filter_cons]
  by_cases h : s.1 = i
  · simp [h]
  · simp [h]

/-- The slot counts of the clients sum to the number of slots. -/
lemma sum_grayTailRootSlotCount {n b : ℕ} (slots : List (GrayTailSlot n b)) :
    (∑ i : Fin n, grayTailRootSlotCount slots i) = slots.length := by
  induction slots with
  | nil =>
      simp [grayTailRootSlotCount]
  | cons s slots ih =>
      simp only [grayTailRootSlotCount_cons, List.length_cons]
      rw [Finset.sum_add_distrib, ih]
      have h1 : (∑ i : Fin n, if s.1 = i then 1 else 0) = 1 := by
        simp
      rw [h1]

/-- Summing the per-root stopping inequalities gives the old aggregate
one-quarter estimate. This is finite list counting only; it uses no game
semantics. -/
theorem grayTail_width_of_perRootQuarter {n b used : ℕ}
    {slots : List (GrayTailSlot n b)}
    (hroot : GrayTailPerRootQuarter used slots) :
    4 * slots.length ≤ n * used := by
  unfold GrayTailPerRootQuarter grayTailPerRootQuarterB at hroot
  rw [List.all_eq_true] at hroot
  have hbound : ∀ i : Fin n, 4 * grayTailRootSlotCount slots i ≤ used := by
    intro i
    have hi := hroot i (List.mem_finRange i)
    simp only [decide_eq_true_eq] at hi
    exact hi
  have hsum : (∑ i : Fin n, 4 * grayTailRootSlotCount slots i) ≤ ∑ i : Fin n, used := by
    apply Finset.sum_le_sum
    intro i _
    exact hbound i
  rw [← Finset.mul_sum, sum_grayTailRootSlotCount] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

/-! ### The three-case transition contract

`grayTailWaitingB` is identically `false`, so one controller transition has
exactly three shapes, fixed by the lemmas of this section:

* a **stalled** tick (`grayTailStep_of_stalled`) — the state is already `done`
  or no slot is active; only the clock advances, every other field is kept;
* a **rejected** round (`grayTailStep_of_rejected`) — the robust gray goal
  fails; the clock and the recursive history advance, everything else is kept;
* an **accepted** round (`grayTailStep_accepted_fields`) — the goal fires and
  the round is frozen; the freshly recomputed below-threshold reserve-free
  candidates continue (a skipped son re-enters when its reserve disappears),
  `anchoringSlots := []`, and the controller stops exactly when the SUV global
  quarter condition holds for the new candidate list or the round cap is
  reached.

Downstream case analyses should consume these lemmas rather than reopening
`grayTailStep`. -/

/-- A terminated tail state only advances its clock. -/
lemma grayTailStep_of_stalled {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (ht : (st.done || st.slots.isEmpty) = true) :
    grayTailStep q L a e sigma A st sm = { st with time := st.time + 1 } := by
  by_cases hd : st.done = true
  · simp [grayTailStep, grayTailWaitingB, hd]
  · have hs : st.slots.isEmpty = true := by
      have hcases := ht
      simp only [Bool.or_eq_true] at hcases
      rcases hcases with h | h
      · exact absurd h hd
      · exact h
    simp [grayTailStep, grayTailWaitingB, hd, hs]

/-- A round that misses the robust gray goal only appends the current move and the localised
server move to the history. -/
lemma grayTailStep_of_rejected {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hd : st.done = false) (hs : st.slots.isEmpty = false)
    (hg : familyRobustGrayGoalAtB (halfAmplification q)
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      st.slots.length st.unavailable
      (grayTailCurrentMove q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = false) :
    grayTailStep q L a e sigma A st sm =
      { st with
          time := st.time + 1
          history := (st.history.1 ++ [grayTailCurrentMove q L e sigma st],
            st.history.2 ++ [grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length) st.slots sm]) } := by
  simp [grayTailStep, grayTailWaitingB, hd, hs, hg]

/-- After a round is frozen, the finished flag is the global quarter test or the round budget
test, and no anchoring slots remain. -/
lemma grayTailStep_accepted_fields {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hd : st.done = false) (hs : st.slots.isEmpty = false)
    (hg : familyRobustGrayGoalAtB (halfAmplification q)
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      st.slots.length st.unavailable
      (grayTailCurrentMove q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots sm) = true) :
    (grayTailStep q L a e sigma A st sm).done =
        (grayTailGlobalQuarterB (n := n) (2 ^ (e - a))
            (grayTailStep q L a e sigma A st sm).slots ||
          decide (grayTailRoundCount q <=
            (grayTailStep q L a e sigma A st sm).frozen.length)) ∧
      (grayTailStep q L a e sigma A st sm).anchoringSlots = [] := by
  refine ⟨?_, ?_⟩ <;>
    simp [grayTailStep, grayTailWaitingB, hd, hs, hg]

/-- A state whose `done` bit was set by the controller satisfies the SUV
global stopping condition: at most one quarter of all source sons is still
unresolved.  In the round-cap branch this uses
`grayTail_slots_eq_nil_of_roundCount_stateAt_global`. -/
theorem grayTail_terminal_width_of_done_stateAt
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hdone : (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done = true) :
    4 * (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).slots.length <= n * 2 ^ (e - a) := by
  induction t with
  | zero =>
      simp [grayTailInitialState] at hdone
  | succ t ih =>
      rw [grayTailStateAt_succ] at hdone ⊢
      set st := grayTailStateAt (n := n) (b := b) q L a e sigma A sm t
      have hdone_step : (grayTailStep q L a e sigma A st (sm t)).done = true := hdone
      by_cases hd : st.done = true
      · rw [grayTailStep_of_stalled q L a e sigma A st (sm t) (by simp [hd])]
        exact ih hd
      · by_cases hs : st.slots.isEmpty = true
        · rw [grayTailStep_of_stalled q L a e sigma A st (sm t) (by simp [hs])]
          have hnil := List.isEmpty_iff.mp hs
          simp [hnil]
        · rw [Bool.not_eq_true] at hd hs
          by_cases hg : familyRobustGrayGoalAtB (halfAmplification q)
              ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
              (grayTailRoundEps q L e st.frozen.length)
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots.length st.unavailable
              (grayTailCurrentMove q L e sigma st)
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length)
                st.slots (sm t)) = true
          · have hfields := grayTailStep_accepted_fields
              q L a e sigma A st (sm t) hd hs hg
            rw [hfields.1] at hdone_step
            by_cases hstop : grayTailGlobalQuarterB (n := n) (2 ^ (e - a))
                (grayTailStep q L a e sigma A st (sm t)).slots = true
            · exact (grayTailGlobalQuarterB_eq_true_iff _ _).mp hstop
            · have hdecide :
                  decide (grayTailRoundCount q <=
                    (grayTailStep q L a e sigma A st (sm t)).frozen.length) = true := by
                simpa [hstop] using hdone_step
              have hcount : grayTailRoundCount q <=
                  (grayTailStep q L a e sigma A st (sm t)).frozen.length :=
                of_decide_eq_true hdecide
              have hcountState : grayTailRoundCount q <=
                  (grayTailStateAt (n := n) (b := b)
                    q L a e sigma A sm (t + 1)).frozen.length := by
                rw [grayTailStateAt_succ]
                exact hcount
              have hnil :=
                grayTail_slots_eq_nil_of_roundCount_stateAt_global hcountState
              rw [grayTailStateAt_succ] at hnil
              rw [hnil]
              simp
          · rw [Bool.not_eq_true] at hg
            have hstep := grayTailStep_of_rejected
              q L a e sigma A st (sm t) hd hs hg
            rw [hstep] at hdone_step ⊢
            exact ih hdone_step

/-- If the gray-tail state at time `t` is terminal - either `done` or with no slots left - then
its width obeys `4 * slots.length ≤ n * 2 ^ (e - a)`.  This is the `done`-only bound
`grayTail_terminal_width_of_done_stateAt` extended to the empty-slot exit. -/
theorem grayTail_terminal_width_stateAt
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots.isEmpty) = true) :
    4 * (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).slots.length <= n * 2 ^ (e - a) := by
  by_cases hdone : (grayTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done = true
  · exact grayTail_terminal_width_of_done_stateAt hdone
  · have hempty : (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots.isEmpty = true := by
      cases hs : (grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).slots.isEmpty with
      | false => simp [hdone, hs] at hterminal
      | true => rfl
    have hnil := List.isEmpty_iff.mp hempty
    rw [hnil]
    simp

end Kolmogorov
