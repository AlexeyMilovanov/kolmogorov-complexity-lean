import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailProgress

/-!
# Per-son flow through the gray-ladder tail

The controller stores slots with a changing grandson coordinate.  For the
terminal accounting we need the stable fact hidden by that representation:
an unresolved root son is carried to the next round exactly when it has not
crossed the threshold and no reserve has appeared.
-/

namespace Kolmogorov

/-- Some open slot of the list sits at the child `c` of client `i`. -/
def GrayTailHasSon {n b : Nat} (slots : List (GrayTailSlot n b))
    (i : Fin n) (c : Fin b) : Prop :=
  ∃ s ∈ slots, s.1 = i ∧ s.2.1 = c

/-- Unfolds to `GrayTailHasSon p.slots i c`: the slot list of the frozen round `p` contains a slot
whose outer root is the client `i` and whose son index is `c`. -/
def GrayTailRoundHasSon {n b : Nat} (p : GrayTailRound n b)
    (i : Fin n) (c : Fin b) : Prop :=
  GrayTailHasSon p.slots i c

/-- The initial slots of a round cover every used child of every client. -/
lemma grayTailHasSon_slots
    {n b used round : Nat} (hr : round < b)
    (i : Fin n) (c : Fin b) (hc : c.val < used) :
    GrayTailHasSon (grayTailSlots n b used round) i c := by
  refine ⟨(i, c, ⟨round, hr⟩), ?_, rfl, rfl⟩
  simp [grayTailSlots, hr, hc]

/-- A child survives into the next round exactly when it is used, still below the threshold and
without a reserve. -/
lemma grayTailHasSon_next_iff
    {n b e used round : Nat} (hr : round < b)
    {threshold : Rat} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    (i : Fin n) (c : Fin b) :
    GrayTailHasSon
        (grayTailNextSlots e used round threshold A frozen sm) i c ↔
      c.val < used ∧
        ¬ threshold < grayTailFrozenSonBase frozen i c ∧
        ¬ (getTailFamilyReserve e b A n i.val sm [c.val]).isSome := by
  classical
  simp [GrayTailHasSon, grayTailNextSlots, hr, and_assoc]

/-- A child is retained exactly when it is both a candidate and currently open. -/
lemma grayTailHasSon_retained_iff {n b : Nat}
    {current candidates : List (GrayTailSlot n b)}
    (i : Fin n) (c : Fin b) :
    GrayTailHasSon (grayTailRetainedSlots current candidates) i c ↔
      GrayTailHasSon candidates i c ∧ GrayTailHasSon current i c := by
  constructor
  · rintro ⟨s, hs, hsi, hsc⟩
    have hcand := (List.mem_filter.mp hs).1
    have hany := (List.mem_filter.mp hs).2
    refine ⟨⟨s, hcand, hsi, hsc⟩, ?_⟩
    rw [List.any_eq_true] at hany
    obtain ⟨old, hold, hsame⟩ := hany
    have heq : s.1 = old.1 ∧ s.2.1 = old.2.1 := by
      simpa [grayTailSameSonB] using hsame
    exact ⟨old, hold, by simpa [hsi] using heq.1.symm,
      by simpa [hsc] using heq.2.symm⟩
  · rintro ⟨⟨s, hs, hsi, hsc⟩, ⟨old, hold, holdi, holdc⟩⟩
    refine ⟨s, List.mem_filter.mpr ⟨hs, ?_⟩, hsi, hsc⟩
    rw [List.any_eq_true]
    refine ⟨old, hold, ?_⟩
    unfold grayTailSameSonB
    simp only [decide_eq_true_eq]
    constructor
    · rw [hsi, holdi]
    · rw [hsc, holdc]

/-- Local removal classification for one firing transition. -/
lemma grayTail_removed_after_freeze
    {n b e used round : Nat} (hr : round < b)
    {threshold : Rat} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {current : List (GrayTailSlot n b)}
    (i : Fin n) (c : Fin b) (hused : c.val < used)
    (hcurrent : GrayTailHasSon current i c)
    (hremoved : ¬ GrayTailHasSon
      (grayTailRetainedSlots current
        (grayTailNextSlots e used round threshold A frozen sm)) i c) :
    threshold < grayTailFrozenSonBase frozen i c ∨
      (getTailFamilyReserve e b A n i.val sm [c.val]).isSome := by
  by_contra h
  push Not at h
  apply hremoved
  rw [grayTailHasSon_retained_iff]
  refine ⟨(grayTailHasSon_next_iff hr i c).2
    ⟨hused, not_lt.mpr h.1, ?_⟩, hcurrent⟩
  simpa using h.2


/-- If the global ordinary-reserve test is false, no represented son has an
ordinary reserve at that server time. -/
lemma grayTail_no_reserve_of_hasSon_of_not_hasUnanchored
    {n b e : Nat} {A : Allocation}
    {slots : List (GrayTailSlot n b)} {server : FamilyServerMove}
    {i : Fin n} {c : Fin b}
    (hson : GrayTailHasSon slots i c)
    (hnone : grayTailHasUnanchoredReserveB e A slots server ≠ true) :
    ¬ (getTailFamilyReserve e b A n i.val server [c.val]).isSome := by
  intro hreserve
  apply hnone
  unfold grayTailHasUnanchoredReserveB
  rw [List.any_eq_true]
  obtain ⟨s, hs, hsi, hsc⟩ := hson
  refine ⟨s, hs, ?_⟩
  simpa [hsi, hsc] using hreserve
/-- A source son omitted by a freshly recomputed candidate list has either
crossed the accumulated-request threshold or has a reserve at this server
time. -/
lemma grayTail_missing_after_freeze
    {n b e used round : Nat} (hr : round < b)
    {threshold : Rat} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    (i : Fin n) (c : Fin b) (hused : c.val < used)
    (hmissing : ¬ GrayTailHasSon
      (grayTailNextSlots e used round threshold A frozen sm) i c) :
    threshold < grayTailFrozenSonBase frozen i c ∨
      (getTailFamilyReserve e b A n i.val sm [c.val]).isSome := by
  by_contra h
  push Not at h
  apply hmissing
  exact (grayTailHasSon_next_iff hr i c).2
    ⟨hused, not_lt.mpr h.1, by simpa using h.2⟩

/-- Disjunction `threshold < grayTailFrozenSonBase frozen i c ∨ ∃ T, (getTailFamilyReserve e b A n
i.val (sm T) [c.val]).isSome`: the son `c` of the outer root `i` has either accumulated frozen
request above `threshold`, or holds an ordinary reserve at some outer server time `T`. -/
def GrayTailSonResolved {n b : Nat} (e : Nat) (threshold : Rat)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (frozen : GrayTailFrozen n b) (i : Fin n) (c : Fin b) : Prop :=
  threshold < grayTailFrozenSonBase frozen i c \/
    exists T, (getTailFamilyReserve e b A n i.val (sm T) [c.val]).isSome

/-- Resolution persists when one certified round is appended. -/
lemma grayTailSonResolved_append
    {n b e : Nat} {threshold : Rat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {frozen : GrayTailFrozen n b}
    {p : GrayTailRound n b} {i : Fin n} {c : Fin b}
    (hnonneg : forall x, x ∈ grayTailSlotEntries p.slots p.move ->
      0 <= getReq x.2 [])
    (h : GrayTailSonResolved e threshold A sm frozen i c) :
    GrayTailSonResolved e threshold A sm (frozen ++ [p]) i c := by
  rcases h with hbase | hreserve
  · left
    rw [grayTailFrozenSonBase_append_global]
    have hp : 0 <=
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c :=
      grayTailSonBase_nonneg_global hnonneg
    linarith
  · exact Or.inr hreserve

/-- For every outer root `i` and every son index `c` with `c.val < 2 ^ (e - a)`: either
`GrayTailHasSon st.slots i c` holds, so the son is still carried by an active slot of `st`, or
`GrayTailSonResolved` holds for it (frozen request above `grayTailThreshold q e`, or a reserve
at some server time). -/
def GrayTailResolutionInvariant {n b : Nat} (q e a : Nat)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailState n b) : Prop :=
  forall i c, c.val < 2 ^ (e - a) ->
    GrayTailHasSon st.slots i c ∨
      GrayTailSonResolved e
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
        A sm st.frozen i c
/-- The tail round count is strictly below the base branching. -/
lemma grayTailRoundCount_lt_baseBranch (q L : Nat) :
    grayTailRoundCount q < grayTailBaseBranch q L := by
  let E := 256 * (q + 1) ^ 2 * L + 256 * (q + 1)
  have hqE : q + 1 <= E := by
    dsimp [E]
    omega
  have hpow : q + 1 < 2 ^ E := by
    calc
      q + 1 < 2 ^ (q + 1) := Nat.lt_two_pow_self
      _ <= 2 ^ E := Nat.pow_le_pow_right (by omega) hqE
  have hqpos : 0 < q + 1 := by omega
  have hstrict :
      256 * (q + 1) ^ 2 <
        256 * (q + 1) * 2 ^ E := by
    calc
      256 * (q + 1) ^ 2 = (256 * (q + 1)) * (q + 1) := by ring
      _ < (256 * (q + 1)) * 2 ^ E := by
        have hfactor : 0 < 256 * (q + 1) := Nat.mul_pos (by norm_num) hqpos
        exact Nat.mul_lt_mul_of_pos_left hpow hfactor
  unfold grayTailRoundCount grayTailBaseBranch
  exact lt_of_lt_of_le hstrict (le_max_right _ _)

/-- A tail step preserves the resolution invariant of the used children. -/
lemma grayTailResolutionInvariant_step
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailState n b)
    (hround : (st.done || st.slots.isEmpty) ≠ true ->
      st.frozen.length + 1 < b)
    (hprev : GrayTailResolutionInvariant q e a A sm st) :
    GrayTailResolutionInvariant q e a A sm
      (grayTailStep q L a e sigma A st (sm t)) := by
  intro i c hused
  unfold grayTailStep
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  next _ =>
    exact hprev i c hused
  next hnotdone =>
    split
    next _ =>
      exact hprev i c hused
    next hnotslots =>
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
        let stop := grayTailGlobalQuarterB (n := n) (2 ^ (e - a)) candidates
        let done' := stop || decide (grayTailRoundCount q ≤ frozen'.length)
        have hactive : (st.done || st.slots.isEmpty) ≠ true := by
          simp [hnotdone, hnotslots]
        have hr : frozen'.length < b := by
          dsimp [frozen']
          simpa using hround hactive
        change GrayTailHasSon candidates i c ∨
          GrayTailSonResolved e threshold A sm frozen' i c
        by_cases hnext : GrayTailHasSon candidates i c
        · exact Or.inl hnext
        · right
          rcases grayTail_missing_after_freeze hr i c hused
              (by simpa [candidates] using hnext) with hbase | hres
          · exact Or.inl (by simpa [threshold, frozen'] using hbase)
          · exact Or.inr ⟨t, hres⟩
      next _ =>
        exact hprev i c hused
/-- Every state of a tail run satisfies the resolution invariant. -/
theorem grayTailResolutionInvariant_stateAt
    {n q L a e : Nat} (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailResolutionInvariant q e a A sm
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      intro i c hused
      left
      apply grayTailHasSon_slots
      · have hb : 2 <= grayTailBranch q L a e :=
          two_le_ladderBranching
            (by unfold grayTailBaseBranch; exact le_max_left _ _) a e
        omega
      · exact hused
  | succ t ih =>
      rw [grayTailStateAt_succ]
      apply grayTailResolutionInvariant_step
        (t := t) (sm := sm) _ _ ih
      intro hactive
      have hlen : (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).frozen.length <
          grayTailRoundCount q := by
        by_contra h
        push Not at h
        have hdone := grayTail_done_of_roundCount_stateAt_core
          (q := q) (L := L) (a := a) (e := e)
          (sigma := sigma) (A := A) (sm := sm) (t := t) h
        apply hactive
        simp [hdone]
      have hbranch :
          grayTailRoundCount q < grayTailBranch q L a e :=
        lt_of_lt_of_le (grayTailRoundCount_lt_baseBranch q L)
          (le_max_right _ _)
      omega

/-- At a terminal state at most one quarter of the source sons remain active,
and every source son is active or has a concrete resolution reason. -/
theorem grayTail_terminal_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    4 * (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.length <= n * 2 ^ (e - a) ∧
      forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
        c.val < 2 ^ (e - a) ->
        GrayTailHasSon
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).slots i c ∨
          GrayTailSonResolved e
            (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
            A sm
            (grayTailStateAt
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).frozen i c := by
  constructor
  · exact grayTail_terminal_width_stateAt hterminal
  · exact grayTailResolutionInvariant_stateAt (n := n) sigma A sm t

end Kolmogorov
