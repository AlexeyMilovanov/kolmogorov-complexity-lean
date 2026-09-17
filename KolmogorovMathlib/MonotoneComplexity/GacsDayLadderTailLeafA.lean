import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs

/-!
# Leaf A of the tail frontier, decomposed

`grayTail_terminal_history` (Leaf A) asserts that one real execution of the
tail controller which does not lose by a positive unserved request reaches a
terminal time carrying the whole finite history certificate
`GrayTailTerminalData`.

Most of its fields are already proved controller invariants.  What is genuinely
missing splits into three strictly narrower statements about one reconstructed
run:

```text
A1  grayTail_exists_terminal_run          replay termination      (proved)
A2  grayTail_frozen_roundIndex_eq_position round chronology       (proved)
A3  grayTail_first_frozen_round_source   the first round is the whole source
                                                                  (proved)
```

All three children are proved, so Leaf A itself is closed.  Everything else -- the certificate,
the terminal width, the two exact exits, the owner split, the displayed
requests, the stability of the outer play -- is assembled here from already
proved theorems.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ### A1: replay termination -/

/-- **Child A1 (proved).**  A run of the tail controller which does not lose by
a positive unserved request reaches a terminal reconstructed state.

This is `grayTail_eventually_terminal_or_positive` started at time `0` with the
full source round budget as fuel. -/
theorem grayTail_exists_terminal_run
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm) :
    ∃ T, ((grayTailRunState q L a e n sigma A sm T).done ||
      (grayTailRunState q L a e n sigma A sm T).slots.isEmpty) = true := by
  have hstart :
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm 0).roundStart = 0 := by
    simp [grayTailInitialState]
  have hbudget : grayTailRoundCount q ≤
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm 0).frozen.length + grayTailRoundCount q := by
    omega
  rcases grayTail_eventually_terminal_or_positive (t := 0)
      (fuel := grayTailRoundCount q)
      ha hae hB hRung hsm hstart hbudget with hwin | ⟨u, _, hu⟩
  · exact absurd hwin hnotwin
  · exact ⟨u, hu⟩

/-! ### A2: the recorded round index is the list position -/

/-! The controller freezes a round with `roundIndex := st.frozen.length` and
never reorders the list, so `A2` is the chronology invariant of the frozen
chain.  It is what makes `grayTailOwnerIndex` -- a *position* -- select the
round whose recorded index it is.  It is proved below from the one-step
invariant. -/

/-- The chronology invariant of a frozen chain: the index recorded inside a
round is its position. -/
def GrayTailChronological {n b : ℕ} (frozen : GrayTailFrozen n b) : Prop :=
  ∀ (r : ℕ) (p : GrayTailRound n b), frozen[r]? = some p → p.roundIndex = r

/-- Appending a round whose recorded index is the current length preserves the
chronology invariant. -/
theorem grayTailChronological_append_self {n b : ℕ} {frozen : GrayTailFrozen n b}
    (h : GrayTailChronological frozen) (p : GrayTailRound n b)
    (hp : p.roundIndex = frozen.length) :
    GrayTailChronological (frozen ++ [p]) := by
  intro r x hx
  rcases lt_or_ge r frozen.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hx
    exact h r x hx
  · rw [List.getElem?_append_right hge] at hx
    have hr0 : r - frozen.length = 0 := by
      by_contra hne
      simp [show ¬ (r - frozen.length < 1) by omega] at hx
    rw [hr0] at hx
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    omega

/-- One controller transition either leaves the frozen chain alone or appends a
round with `roundIndex := st.frozen.length`, so it preserves chronology. -/
theorem grayTailStep_chronological {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    {st : GrayTailState n b} (sm : FamilyServerMove)
    (hst : GrayTailChronological st.frozen) :
    GrayTailChronological (grayTailStep q L a e sigma A st sm).frozen := by
  rw [grayTailStep]
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hst
  · split
    · exact hst
    · split
      · exact grayTailChronological_append_self hst _ rfl
      · exact hst

/-- Every reconstructed controller state is chronological. -/
theorem grayTailStateAt_chronological {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (T : ℕ) :
    GrayTailChronological
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).frozen := by
  induction T with
  | zero => intro r p hp; simp [grayTailStateAt_zero, grayTailInitialState] at hp
  | succ T ih =>
      rw [grayTailStateAt_succ]
      exact grayTailStep_chronological q L a e sigma A (sm T) ih

/-- **Child A2 (proved).**  The round index recorded inside a frozen round is
its position in the frozen list. -/
theorem grayTail_frozen_roundIndex_eq_position
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (r : ℕ) (hr : r < (grayTailRunState q L a e n sigma A sm T).frozen.length) :
    ((grayTailRunState q L a e n sigma A sm T).frozen.get ⟨r, hr⟩).roundIndex = r := by
  have h := grayTailStateAt_chronological (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm T
  rw [List.get_eq_getElem]
  exact h r _ (List.getElem?_eq_getElem hr)

/-! ### A3: the first frozen round contains every source son -/

/-! The controller freezes its first round out of the initial state, whose
slots are `grayTailSlots n b (2 ^ (e - a)) 0`; no other round has recorded
index `0`.  `A3` is proved below from that invariant together with the exact
length of the initial slot list. -/

/-- Every value below `used` occurs in the filtered range. -/
theorem range_filter_lt_eq (used b : ℕ) :
    (List.range b).filter (fun i => decide (i < used)) = List.range (min used b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.filter_append, ih]
    rcases Nat.lt_or_ge b used with hb | hb
    · have h1 : min used b = b := Nat.min_eq_right (le_of_lt hb)
      simp [h1, hb, List.range_succ]
    · have h1 : min used b = used := Nat.min_eq_left hb
      have h2 : min used (b + 1) = used := Nat.min_eq_left (by omega)
      simp [h1, h2, Nat.not_lt.mpr hb]

/-- Exactly `used` of the `b` children survive the source filter. -/
theorem finRange_filter_lt_length (b used : ℕ) (h : used ≤ b) :
    ((List.finRange b).filter (fun c : Fin b => decide (c.val < used))).length = used := by
  have hmap : ((List.finRange b).filter
      (fun c : Fin b => decide (c.val < used))).map (fun x : Fin b => (x : ℕ))
      = (List.range b).filter (fun i => decide (i < used)) := by
    rw [← List.map_coe_finRange_eq_range (n := b), List.filter_map]
    rfl
  have hlen := congrArg List.length hmap
  rw [List.length_map, range_filter_lt_eq, List.length_range, Nat.min_eq_left h] at hlen
  exact hlen

/-- The initial slot list of a round is the whole source family. -/
theorem grayTailSlots_length (n b used r : ℕ) (hr : r < b) (h : used ≤ b) :
    (grayTailSlots n b used r).length = n * used := by
  unfold grayTailSlots
  rw [dif_pos hr, List.length_flatMap]
  simp [finRange_filter_lt_length b used h]

/-- The controller has not yet frozen anything exactly while its slot list is
still the full source family, and a round recorded with index `0` was frozen
out of such a state. -/
def GrayTailSourceFirst {n b : ℕ} (a e : ℕ) (st : GrayTailState n b) : Prop :=
  (st.frozen = [] → st.slots = grayTailSlots n b (2 ^ (e - a)) 0) ∧
    (∀ p ∈ st.frozen, p.roundIndex = 0 →
      p.slots = grayTailSlots n b (2 ^ (e - a)) 0)

/-- One controller transition preserves the source-first invariant. -/
theorem grayTailStep_sourceFirst {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    {st : GrayTailState n b} (sm : FamilyServerMove)
    (hst : GrayTailSourceFirst a e st) :
    GrayTailSourceFirst a e (grayTailStep q L a e sigma A st sm) := by
  rw [grayTailStep]
  simp only [grayTailWaitingB, Bool.false_eq_true, if_false]
  split
  · exact hst
  · split
    · exact hst
    · split
      · refine ⟨by simp, ?_⟩
        intro p hp hp0
        rcases List.mem_append.mp hp with hmem | hmem
        · exact hst.2 p hmem hp0
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          subst hmem
          simp only at hp0
          exact hst.1 (List.eq_nil_of_length_eq_zero hp0)
      · exact hst

/-- Every reconstructed controller state satisfies the source-first
invariant. -/
theorem grayTailStateAt_sourceFirst {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (T : ℕ) :
    GrayTailSourceFirst a e
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T) := by
  induction T with
  | zero => exact ⟨fun _ => rfl, by simp [grayTailStateAt_zero, grayTailInitialState]⟩
  | succ T ih =>
      rw [grayTailStateAt_succ]
      exact grayTailStep_sourceFirst q L a e sigma A (sm T) ih

/-- **Child A3 (proved).**  The first frozen round of a run is planted on the
whole source family: it contains every source son, and its slot list is at
least as long as the source family. -/
theorem grayTail_first_frozen_round_source
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (p : GrayTailRound n (grayTailBranch q L a e))
    (hp : p ∈ (grayTailRunState q L a e n sigma A sm T).frozen)
    (hindex : p.roundIndex = 0) :
    (∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)), c.val < 2 ^ (e - a) →
        GrayTailRoundHasSon p i c) ∧
      n * 2 ^ (e - a) ≤ p.slots.length := by
  have hused : 2 ^ (e - a) ≤ grayTailBranch q L a e := by
    simp only [grayTailBranch, ladderBranching]
    exact le_trans (by omega) (le_max_left _ _)
  have hpos : 0 < grayTailBranch q L a e :=
    lt_of_lt_of_le (Nat.two_pow_pos _) hused
  have hslots : p.slots
      = grayTailSlots n (grayTailBranch q L a e) (2 ^ (e - a)) 0 :=
    (grayTailStateAt_sourceFirst (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T).2 p hp hindex
  refine ⟨fun i c hc => ?_, ?_⟩
  · rw [GrayTailRoundHasSon, hslots]
    exact grayTailHasSon_slots hpos i c hc
  · rw [hslots, grayTailSlots_length _ _ _ _ hpos hused]

/-! ### The displayed requests of a terminal state -/

/-- The displayed son request of a terminal state is the accumulated frozen
increment, raised to `epsilon` exactly above the source threshold. -/
theorem grayTail_terminal_displayed_son_request
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hterminal : ((grayTailRunState q L a e n sigma A sm T).done ||
      (grayTailRunState q L a e n sigma A sm T).slots.isEmpty) = true)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [c.val] =
      (if grayTailThreshold q e <
          grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c
        then dyadicScale e
        else grayTailFrozenSonBase
          (grayTailRunState q L a e n sigma A sm T).frozen i c) := by
  rw [grayTailRunMove, getFamilyReq_grayTailOutput_son _ i.isLt c.isLt]
  unfold grayTailSonRequest
  rw [grayTail_terminal_sonBase_eq_frozen hterminal]

/-- The displayed root request of a terminal state is the son sum lifted to the
terminal floor. -/
theorem grayTail_terminal_displayed_root_request
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hdone : (grayTailRunState q L a e n sigma A sm T).done = true)
    (i : Fin n) :
    getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [] =
      max (∑ c : Fin (grayTailBranch q L a e),
            getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [c.val])
        (grayTailTargetFloor q a) := by
  have hterminal : ((grayTailRunState q L a e n sigma A sm T).done ||
      (grayTailRunState q L a e n sigma A sm T).slots.isEmpty) = true := by
    simp [hdone]
  have hson : ∀ c : Fin (grayTailBranch q L a e),
      getFamilyReq (grayTailRunMove q L a e n sigma A sm T) i.val [c.val] =
        grayTailSonRequest (grayTailThreshold q e) (dyadicScale e)
          (grayTailEntries (grayTailRunState q L a e n sigma A sm T).frozen
            (grayTailRunState q L a e n sigma A sm T).slots
            (if (grayTailRunState q L a e n sigma A sm T).done then []
              else grayTailCurrentMove q L e sigma
                (grayTailRunState q L a e n sigma A sm T))) i c := by
    intro c
    rw [grayTailRunMove, getFamilyReq_grayTailOutput_son _ i.isLt c.isLt]
  rw [grayTailRunMove, getFamilyReq_grayTailOutput_root _ i.isLt]
  unfold grayTailRootRequest
  rw [if_pos hdone]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hson c]

/-! ### Leaf A, assembled from its children -/

/-- **Leaf A (parent).**  One real tail-controller execution which does not
lose by a positive unserved request reaches a terminal time carrying the full
finite history certificate.

The proof is pure assembly: `A1` supplies the terminal time, `A2` and `A3`
supply the chronology of the frozen list, and every other field is one of the
already proved controller invariants
(`grayTailCertified_stateAt`, `grayTail_done_of_terminal`,
`playClientFamily_grayTailStrategy_stable`, `grayTailWidthInvariant_stateAt`,
`grayTail_terminal_width_stateAt`, `grayTail_frozen_sonBase_eq_zero_of_source_ge`,
`grayTail_all_frozen_base_le_stateAt`,
`grayTail_terminal_detailed_resolution`,
`grayTail_terminal_ownerSplit_existsUnique`). -/
theorem grayTail_terminal_history
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hn : 1 ≤ n)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm) :
    ∃ T, GrayTailTerminalData q L a e n sigma A sm T := by
  classical
  obtain ⟨T, hterminal⟩ :=
    grayTail_exists_terminal_run ha hae hB hRung hsm hnotwin
  have hdone : (grayTailRunState q L a e n sigma A sm T).done = true :=
    grayTail_done_of_terminal hn hterminal
  refine ⟨T, ?_⟩
  refine
    { certified := grayTailCertified_stateAt q L a e sigma A sm T
      done := hdone
      round_index_eq := fun r hr => grayTail_frozen_roundIndex_eq_position r hr
      play_eq := ?_
      terminal_width := grayTail_terminal_width_stateAt hterminal
      round_width := ?_
      first_round := ?_
      son_request_eq := grayTail_terminal_displayed_son_request hterminal
      root_request_eq := grayTail_terminal_displayed_root_request hdone
      unused_zero := ?_
      son_base_le := grayTail_all_frozen_base_le_stateAt q L a e sigma A sm T
      exits := grayTail_terminal_detailed_resolution hterminal
      owner_split := ?_ }
  · intro U hU
    rw [playClientFamily_grayTailStrategy_stable sigma A sm hU hterminal,
      playClientFamily_grayTailStrategy q L a e n sigma A sm T]
  · -- every started round contains more than a quarter of the source sons
    intro p hp
    have hnpos : 0 < n * 2 ^ (e - a) :=
      Nat.mul_pos hn (Nat.two_pow_pos _)
    by_cases h0 : p.roundIndex = 0
    · have := (grayTail_first_frozen_round_source p hp h0).2
      omega
    · -- a later round is in the tail of the frozen list
      obtain ⟨r, hr, hpr⟩ := List.mem_iff_getElem.mp hp
      have hidx := grayTail_frozen_roundIndex_eq_position (q := q) (L := L)
        (a := a) (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm)
        (T := T) r hr
      rw [List.get_eq_getElem, hpr] at hidx
      have hrpos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact absurd (hidx.trans h) h0
        · exact h
      have hmemtail : p ∈ (grayTailRunState q L a e n sigma A sm T).frozen.tail := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hlen : r' < (grayTailRunState q L a e n sigma A sm T).frozen.tail.length := by
          rw [List.length_tail]; omega
        have hget : (grayTailRunState q L a e n sigma A sm T).frozen.tail[r'] = p := by
          rw [List.getElem_tail]; exact hpr
        exact hget ▸ List.getElem_mem hlen
      exact (grayTailWidthInvariant_stateAt (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm T).frozenTail p hmemtail
  · intro p hp h0 i c hc
    exact (grayTail_first_frozen_round_source p hp h0).1 i c hc
  · intro i c hc
    exact grayTail_frozen_sonBase_eq_zero_of_source_ge i c (by omega)
  · intro i c hc hinactive
    exact grayTailOwnerIndex_spec
      ((grayTail_terminal_ownerSplit_existsUnique hterminal i c hc hinactive).exists)

end Kolmogorov
