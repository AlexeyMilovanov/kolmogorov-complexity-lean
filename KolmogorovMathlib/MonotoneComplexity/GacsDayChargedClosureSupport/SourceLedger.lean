import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore

/-!
# Gacs-Day charged closure: source ledger

Section 8.2: service and reserve witnesses on the non-positive branch.
-/

namespace Kolmogorov

/-! ## Section 8.2: service and reserve witnesses on the non-positive branch -/

/-- On the non-positive branch every positive displayed request is served at
some finite later server time. -/
lemma grayCharged_exists_serves_of_not_positive
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    {i : Nat} (hi : i < n) (t : Nat) (x : GacsDayNode)
    (hlen : x.length <= 2 * (q + 1))
    (hx : forall d, d ∈ x -> d < grayTailBranch q L a e)
    (hpos : 0 < getFamilyReq (grayChargedRunMove q L a e n sigma A sm t) i x) :
    exists u, Serves (getFamilyAlloc (sm u) i x)
      (getFamilyReq (grayChargedRunMove q L a e n sigma A sm t) i x) := by
  by_contra hcon
  push Not at hcon
  exact hnotpos ⟨i, hi, t, x, hlen, hx, fun u => hcon u, hpos⟩

/-- On the non-positive branch a displayed request of at least one coarse
unit produces a genuine tail family reserve at some finite server time. -/
lemma grayCharged_exists_reserve_of_not_positive
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    {i : Nat} (hi : i < n) (t : Nat) (x : GacsDayNode)
    (hlen : x.length <= 2 * (q + 1))
    (hx : forall d, d ∈ x -> d < grayTailBranch q L a e)
    (hreq : dyadicScale e <=
      getFamilyReq (grayChargedRunMove q L a e n sigma A sm t) i x) :
    exists u R, IsTailFamilyReserve e (grayTailBranch q L a e) A n i
      (sm u) x R := by
  have hpos : 0 < getFamilyReq
      (grayChargedRunMove q L a e n sigma A sm t) i x :=
    lt_of_lt_of_le (dyadicScale_pos e) hreq
  obtain ⟨u, hu⟩ :=
    grayCharged_exists_serves_of_not_positive hnotpos hi t x hlen hx hpos
  obtain ⟨c, hc, hcle⟩ := hu
  have hserve : Serves (getFamilyAlloc (sm u) i x) (dyadicScale e) := by
    refine ⟨c, hc, le_trans ?_ hcle⟩
    exact_mod_cast hreq
  exact ⟨u, exists_tailFamilyReserve_of_serves hsm hi hx hserve⟩

/-! ## Section 8.1: the resolved source ledger and its exact cardinality

The two disjoint resolved classes are the controller's own candidate filter,
read off the replayed advantage exit.  Their union together with the tested
candidate list partitions the whole source population, which is what turns
the terminal quarter-width test into the global three-quarters count. -/

open Classical in
/-- Sources whose frozen son base already exceeds the controller threshold, so
that the controller raised their displayed request to a full coarse unit. -/
noncomputable def grayChargedRaisedSources {n b : Nat} (used : Nat)
    (threshold : Rat) (frozen : GrayTailFrozen n b) :
    Finset (Fin n × Fin b) :=
  Finset.univ.filter fun z =>
    z.2.val < used ∧ threshold < grayTailFrozenSonBase frozen z.1 z.2

open Classical in
/-- Sources below the threshold for which the server has already produced a
reserve at the tested server move. -/
noncomputable def grayChargedServerResolvedSources {n b : Nat}
    (e used : Nat) (threshold : Rat) (A : Allocation)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) :
    Finset (Fin n × Fin b) :=
  Finset.univ.filter fun z =>
    z.2.val < used ∧ ¬ threshold < grayTailFrozenSonBase frozen z.1 z.2 ∧
      (getTailFamilyReserve e b A n z.1.val sm [z.2.val]).isSome

/-- Every raised source coordinate has source index below the number of used sources. -/
lemma grayChargedRaisedSources_source_lt {n b : Nat} {used : Nat} {threshold : Rat}
    {frozen : GrayTailFrozen n b} {z : Fin n × Fin b}
    (hz : z ∈ grayChargedRaisedSources used threshold frozen) :
    z.2.val < used := by
  classical
  simpa [grayChargedRaisedSources] using (Finset.mem_filter.mp hz).2.1

/-- A source resolved by the server lies in the used range of children, below `used`. -/
lemma grayChargedServerResolvedSources_source_lt {n b : Nat} {e used : Nat} {threshold : Rat}
    {A : Allocation} {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    {z : Fin n × Fin b}
    (hz : z ∈ grayChargedServerResolvedSources e used threshold A frozen sm) :
    z.2.val < used := by
  classical
  simpa [grayChargedServerResolvedSources] using
    (Finset.mem_filter.mp hz).2.1

/-- The sources raised by the client and the sources resolved by the server are disjoint. -/
lemma grayChargedSourceClasses_disjoint {n b : Nat} {e used : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} :
    Disjoint (grayChargedRaisedSources (n := n) (b := b) used threshold frozen)
      (grayChargedServerResolvedSources e used threshold A frozen sm) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro z hz hz'
  have h1 := (Finset.mem_filter.mp hz).2
  have h2 := (Finset.mem_filter.mp hz').2
  
  exact h2.2.1 h1.2

/-- Membership in the union of the two resolved classes. -/
lemma mem_grayChargedResolvedSources_union {n b : Nat} {e used : Nat} {threshold : Rat}
    {A : Allocation} {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    (z : Fin n × Fin b) :
    z ∈ grayChargedRaisedSources (n := n) (b := b) used threshold frozen ∪
        grayChargedServerResolvedSources e used threshold A frozen sm ↔
      z.2.val < used ∧
        ¬ (¬ threshold < grayTailFrozenSonBase frozen z.1 z.2 ∧
            ¬ (getTailFamilyReserve e b A n z.1.val sm [z.2.val]).isSome) := by
  classical
  simp only [Finset.mem_union, grayChargedRaisedSources,
    grayChargedServerResolvedSources, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨hu, hb⟩ | ⟨hu, hb, hr⟩)
    · exact ⟨hu, fun h => h.1 hb⟩
    · exact ⟨hu, fun h => h.2 hr⟩
  · rintro ⟨hu, h⟩
    by_cases hb : threshold < grayTailFrozenSonBase frozen z.1 z.2
    · exact Or.inl ⟨hu, hb⟩
    · refine Or.inr ⟨hu, hb, ?_⟩
      by_contra hr
      exact h ⟨hb, hr⟩

/-- The slab of coordinates whose child index is below `used ≤ b` has exactly `n * used`
elements. -/
lemma grayCharged_card_source_slab (n b used : Nat) (hused : used <= b) :
    (Finset.univ.filter fun z : Fin n × Fin b => z.2.val < used).card =
      n * used := by
  classical
  have hprod : (Finset.univ.filter fun z : Fin n × Fin b => z.2.val < used) =
      (Finset.univ : Finset (Fin n)) ×ˢ
        (Finset.univ.filter fun c : Fin b => c.val < used) := by
    ext z
    simp [Finset.mem_product]
  have himg : ((Finset.univ.filter fun c : Fin b => c.val < used).image
      Fin.val) = Finset.range used := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hm
      exact ⟨⟨m, lt_of_lt_of_le hm hused⟩, hm, rfl⟩
  have hcard : (Finset.univ.filter fun c : Fin b => c.val < used).card =
      used := by
    have := congrArg Finset.card himg
    rwa [Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_range] at this
  rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin, hcard]

/-- The slots carried into the next round are exactly the coordinates of the source slab that are
neither raised nor resolved by the server. -/
lemma grayTailNextSlots_length_eq_unresolved_card {n b : Nat} {e used round : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} (hr : round < b) :
    (grayTailNextSlots e used round threshold A frozen sm).length =
      ((Finset.univ.filter fun z : Fin n × Fin b => z.2.val < used) \
        (grayChargedRaisedSources used threshold frozen ∪
          grayChargedServerResolvedSources e used threshold A frozen sm)).card
      := by
  classical
  set l := grayTailNextSlots e used round threshold A frozen sm with hl
  have hnodup : l.Nodup := grayTailNextSlots_nodup _ _ _ _ _ _ _
  have hround : forall s, s ∈ l -> s.2.2.val = round := fun s hs =>
    grayTailNextSlots_round hs
  have hmapNodup : (l.map fun s => (s.1, s.2.1)).Nodup := by
    refine List.Nodup.map_on ?_ hnodup
    intro s hs t ht hst
    obtain ⟨h1, h2⟩ := Prod.mk.inj hst
    have h3 : s.2.2 = t.2.2 := by
      apply Fin.ext
      rw [hround s hs, hround t ht]
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hmem : forall z : Fin n × Fin b,
      z ∈ (l.map fun s => (s.1, s.2.1)) ↔
        z ∈ (Finset.univ.filter fun z : Fin n × Fin b => z.2.val < used) \
          (grayChargedRaisedSources used threshold frozen ∪
            grayChargedServerResolvedSources e used threshold A frozen sm) := by
    intro z
    have hson : (z ∈ (l.map fun s => (s.1, s.2.1))) ↔
        GrayTailHasSon l z.1 z.2 := by
      simp only [List.mem_map, GrayTailHasSon]
      constructor
      · rintro ⟨s, hs, hsz⟩
        exact ⟨s, hs, congrArg Prod.fst hsz, congrArg Prod.snd hsz⟩
      · rintro ⟨s, hs, h1, h2⟩
        exact ⟨s, hs, Prod.ext h1 h2⟩
    rw [hson, hl, grayTailHasSon_next_iff hr]
    rw [Finset.mem_sdiff, Finset.mem_filter]
    rw [mem_grayChargedResolvedSources_union]
    simp only [Finset.mem_univ, true_and]
    tauto
  have hlen : l.length = (l.map fun s => (s.1, s.2.1)).length := by simp
  rw [hlen, ← List.toFinset_card_of_nodup hmapNodup]
  congr 1
  ext z
  rw [List.mem_toFinset]
  exact hmem z

/-- Section 8.1: the resolved sources and the tested candidate slots exactly
partition the whole source population. -/
lemma grayCharged_resolved_card_add_nextSlots_length {n b : Nat} {e used round : Nat}
    {threshold : Rat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {sm : FamilyServerMove} (hr : round < b) (hused : used <= b) :
    (grayChargedRaisedSources (n := n) (b := b) used threshold frozen ∪
        grayChargedServerResolvedSources e used threshold A frozen sm).card +
      (grayTailNextSlots e used round threshold A frozen sm).length =
      n * used := by
  classical
  have hsub : (grayChargedRaisedSources (n := n) (b := b) used threshold frozen ∪
      grayChargedServerResolvedSources e used threshold A frozen sm) ⊆
      Finset.univ.filter fun z : Fin n × Fin b => z.2.val < used := by
    intro z hz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ z, (mem_grayChargedResolvedSources_union z).mp hz |>.1⟩
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  rw [grayTailNextSlots_length_eq_unresolved_card hr]
  rw [grayCharged_card_source_slab n b used hused] at hsplit
  omega

/-- A tail step that leaves the tail active keeps the number of frozen rounds below the advantage
round budget `grayChargedAdvantageRoundCount q`. -/
lemma grayChargedTailStep_frozen_length_lt_roundCount {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (m : FamilyServerMove)
    (hst : st.done = false ->
      st.frozen.length < grayChargedAdvantageRoundCount q)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = false) :
    (grayChargedTailStep q L a e sigma A st m).frozen.length <
      grayChargedAdvantageRoundCount q := by
  rw [grayChargedTailStep_eq] at hdone ⊢
  by_cases hterm : (st.done || st.slots.isEmpty) = true
  · rw [ite_eq_left hterm] at hdone ⊢
    exact hst hdone
  · rw [ite_eq_right hterm] at hdone ⊢
    by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · rw [ite_eq_left hgoal] at hdone ⊢
      dsimp only at hdone ⊢
      have h := Bool.or_eq_false_iff.mp hdone
      have hfour := grayTailRoundCount_eight_lt q
      have hlt : st.frozen.length + 1 + 8 < grayTailRoundCount q := by
        have hd3 : ¬ (grayChargedAdvantageRoundCount q ≤ List.length st.frozen + 1) := by
          have h2_false := h.2
          simp only [List.length_append, List.length_singleton] at h2_false
          exact decide_eq_false_iff_not.mp h2_false
        unfold grayChargedAdvantageRoundCount at hd3
        omega
      simp only [List.length_append, List.length_singleton] at ⊢
      unfold grayChargedAdvantageRoundCount
      omega
    · rw [ite_eq_right hgoal] at hdone ⊢
      dsimp only at hdone ⊢
      exact hst hdone

/-- While the tail is still active, it has frozen fewer rounds than the advantage round budget
`grayChargedAdvantageRoundCount q`. -/
lemma grayChargedTailStateAt_frozen_length_lt_roundCount {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    (grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done = false ->
    (grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).frozen.length <
      grayChargedAdvantageRoundCount q := by
  induction t with
  | zero =>
      intro _
      have h0 : (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm 0).frozen = [] := rfl
      rw [h0]
      simpa using grayChargedAdvantageRoundCount_pos q
  | succ t ih =>
      intro hdone
      rw [grayChargedTailStateAt_succ] at hdone ⊢
      exact grayChargedTailStep_frozen_length_lt_roundCount q L a e sigma A _ (sm t) ih hdone



/-- A tail step that finishes the tail freezes exactly one further round, and its surviving slots
are the unresolved coordinates of that round. -/
lemma grayChargedTailStep_freeze_shape_of_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = true) :
    (grayChargedTailStep q L a e sigma A st m).frozen.length =
        st.frozen.length + 1 ∧
      (grayChargedTailStep q L a e sigma A st m).slots =
        grayTailNextSlots e (grayChargedSourceCount a e)
          (grayChargedTailStep q L a e sigma A st m).frozen.length
          (grayChargedThreshold q e) A
          (grayChargedTailStep q L a e sigma A st m).frozen m := by
  rw [grayChargedTailStep_eq] at hdone ⊢
  by_cases hslots : st.slots.isEmpty = true
  · rw [ite_eq_left (by simp [hslots])] at hdone
    simp [hactive] at hdone
  · rw [ite_eq_right (by simp [hactive, hslots])] at hdone ⊢
    by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · rw [ite_eq_left hgoal] at hdone ⊢
      dsimp only
      exact ⟨by simp, rfl⟩
    · rw [ite_eq_right hgoal] at hdone
      dsimp only at hdone
      rw [hactive] at hdone
      exact absurd hdone (by simp)


/-- The source children fit inside the branching of the tail: `grayChargedSourceCount a e` is at
most `grayTailBranch q L a e`. -/
lemma grayChargedSourceCount_le_grayTailBranch (q L a e : Nat) :
    grayChargedSourceCount a e <= grayTailBranch q L a e := by
  have h : 2 * 2 ^ (e - a) <= grayTailBranch q L a e := by
    simp [grayTailBranch, ladderBranching]
  have h2 : grayChargedSourceCount a e <= 2 * 2 ^ (e - a) := by
    simp [grayChargedSourceCount]
  exact le_trans h2 h

/-- Section 8.1: at the advantage exit the two resolved source classes and the
tested candidate slots partition the whole source population exactly. -/
theorem grayCharged_resolved_source_count_at_exit
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (terminal : GrayTailState n (grayTailBranch q L a e))
    (hterminal : terminal = grayChargedTailStep q L a e sigma A
      (grayChargedRunState q L a e n sigma A sm t).core (sm t))
    (hbefore :
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage)
    (hafter :
      (grayChargedRunState q L a e n sigma A sm (t + 1)).phase ≠
        .advantage) :
    (grayChargedRaisedSources (grayChargedSourceCount a e)
          (grayChargedThreshold q e) terminal.frozen ∪
        grayChargedServerResolvedSources e (grayChargedSourceCount a e)
          (grayChargedThreshold q e) A terminal.frozen (sm t)).card +
      terminal.slots.length = n * grayChargedSourceCount a e := by
  classical
  have hactive := grayChargedRunState_core_done_false_of_advantage hbefore
  have hdone := grayCharged_advantage_exit_terminal_done hbefore hafter
  have hcore := grayChargedStateAt_core_eq_tailStateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t hbefore
  have hshape := grayChargedTailStep_freeze_shape_of_done q L a e sigma A
    (grayChargedRunState q L a e n sigma A sm t).core (sm t) hactive hdone
  have hfrozenLt : (grayChargedRunState q L a e n sigma A sm t).core.frozen.length <
      grayChargedAdvantageRoundCount q := by
    rw [hcore]
    exact grayChargedTailStateAt_frozen_length_lt_roundCount q L a e sigma A sm t (by rw [← hcore];
                                                                                       exact
      hactive)
  have hround : terminal.frozen.length < grayTailBranch q L a e := by
    rw [hterminal, hshape.1]
    exact lt_of_le_of_lt (by omega) (grayChargedAdvantageRoundCount_lt_grayTailBranch q L a e)
  have hslots : terminal.slots =
      grayTailNextSlots e (grayChargedSourceCount a e) terminal.frozen.length
        (grayChargedThreshold q e) A terminal.frozen (sm t) := by
    rw [hterminal]
    exact hshape.2
  rw [hslots]
  exact grayCharged_resolved_card_add_nextSlots_length hround
    (grayChargedSourceCount_le_grayTailBranch q L a e)

/-- The resolved source ledger of a final replay: the two disjoint classes are
computed at the saved advantage exit. -/
noncomputable def grayChargedReplayRaisedSources
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    Finset (Fin n × Fin (grayTailBranch q L a e)) :=
  grayChargedRaisedSources (grayChargedSourceCount a e)
    (grayChargedThreshold q e) replay.advantageTerminal.frozen

/-- The coordinates that the server resolved by the exit time of the `advantage` phase of a final
replay. -/
noncomputable def grayChargedReplayServerResolvedSources
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    Finset (Fin n × Fin (grayTailBranch q L a e)) :=
  grayChargedServerResolvedSources e (grayChargedSourceCount a e)
    (grayChargedThreshold q e) A replay.advantageTerminal.frozen
    (sm replay.advantageExitTime)

/-- The resolved coordinates of a replay and the slots surviving its terminal state together
exhaust the source slab of `n * grayChargedSourceCount a e` coordinates. -/
theorem grayChargedReplay_resolvedSourceCount_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    (grayChargedReplayRaisedSources replay ∪
        grayChargedReplayServerResolvedSources replay).card +
      replay.advantageTerminal.slots.length =
      n * grayChargedSourceCount a e :=
  grayCharged_resolved_source_count_at_exit replay.advantageTerminal
    replay.advantageTerminal_eq replay.advantage_before replay.advantage_after

/-- At least three quarters of the source slab is resolved by the end of the `advantage` phase. -/
theorem grayChargedReplay_resolved_three_quarters
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    3 * (n * grayChargedSourceCount a e) <=
      4 * (grayChargedReplayRaisedSources replay ∪
        grayChargedReplayServerResolvedSources replay).card := by
  have heq := grayChargedReplay_resolvedSourceCount_eq replay
  have hw := replay.terminal_width
  omega

/-! ## Exact chronology and owner rounds at the advantage exit -/

/-- The terminal state recorded by a replay is the tail state one step after the exit time of the
`advantage` phase. -/
lemma grayChargedReplay_advantageTerminal_eq_stateAt
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    replay.advantageTerminal =
      grayChargedTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (replay.advantageExitTime + 1) := by
  rw [replay.advantageTerminal_eq, grayChargedTailStateAt_succ]
  congr 1
  exact grayChargedStateAt_core_eq_tailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm replay.advantageExitTime replay.advantage_before

/-- The terminal state recorded by a replay has the tail finished. -/
lemma grayChargedReplay_advantageTerminal_done
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    replay.advantageTerminal.done = true := by
  rw [replay.advantageTerminal_eq]
  exact grayCharged_advantage_exit_terminal_done
    replay.advantage_before replay.advantage_after

/-- The exact charged chronology at the replayed advantage exit.  Unlike the
coarse raised/server-resolved partition, this theorem retains the last-call
decomposition and a persistent reserve witness on the low-base branch. -/
theorem grayChargedReplay_terminal_detailed_resolution
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hused : c.val < grayChargedSourceCount a e)
    (hinactive : ¬ GrayTailHasSon replay.advantageTerminal.slots i c) :
    ((grayChargedThreshold q e <
          grayTailFrozenSonBase replay.advantageTerminal.frozen i c) ∧
        GrayTailThresholdExit e A sm
          replay.advantageTerminal.frozen i c) ∨
      (GrayTailPersistentReserveExit e A sm
          replay.advantageTerminal.frozen i c ∧
        grayTailFrozenSonBase replay.advantageTerminal.frozen i c <=
          grayChargedThreshold q e) := by
  have heq := grayChargedReplay_advantageTerminal_eq_stateAt replay
  have hterminal :
      ((grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (replay.advantageExitTime + 1)).done ||
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm
            (replay.advantageExitTime + 1)).slots.isEmpty) = true := by
    rw [← heq]
    simp [grayChargedReplay_advantageTerminal_done replay]
  have hinactive' :
      ¬ GrayTailHasSon
        (grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm
            (replay.advantageExitTime + 1)).slots i c := by
    rw [← heq]
    exact hinactive
  have hres := grayChargedTail_terminal_detailed_resolution
    hterminal i c hused hinactive'
  rw [← heq] at hres
  simpa [grayChargedThreshold] using hres

/-- Source-level data retained for one resolved source.  The owner index is
the unique last frozen round containing the source; the resolution field keeps
the threshold or persistent-reserve branch needed by final accounting. -/
structure GrayChargedResolvedSourceChronology
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e)) : Type where
  source_lt : z.2.val < grayChargedSourceCount a e
  inactive : ¬ GrayTailHasSon replay.advantageTerminal.slots z.1 z.2
  resolution :
    ((grayChargedThreshold q e <
          grayTailFrozenSonBase replay.advantageTerminal.frozen z.1 z.2) ∧
        GrayTailThresholdExit e A sm
          replay.advantageTerminal.frozen z.1 z.2) ∨
      (GrayTailPersistentReserveExit e A sm
          replay.advantageTerminal.frozen z.1 z.2 ∧
        grayTailFrozenSonBase replay.advantageTerminal.frozen z.1 z.2 <=
          grayChargedThreshold q e)
  ownerIndex : Nat
  ownerSplit : GrayTailOwnerSplitAt
    replay.advantageTerminal.frozen z.1 z.2 ownerIndex

/-- Every resolved coordinate of a replay carries a chronology: a record of the round and time at
which it was resolved. -/
theorem grayChargedReplay_resolved_source_chronology
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayRaisedSources replay ∪
      grayChargedReplayServerResolvedSources replay) :
    Nonempty (GrayChargedResolvedSourceChronology replay z) := by
  classical
  have hsource := (mem_grayChargedResolvedSources_union z).mp hz
  have hactive := grayChargedRunState_core_done_false_of_advantage
    replay.advantage_before
  have hdone := grayCharged_advantage_exit_terminal_done
    replay.advantage_before replay.advantage_after
  have hshape := grayChargedTailStep_freeze_shape_of_done
    q L a e sigma A
    (grayChargedRunState q L a e n sigma A sm
      replay.advantageExitTime).core
    (sm replay.advantageExitTime) hactive hdone
  have hcore := grayChargedStateAt_core_eq_tailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm replay.advantageExitTime replay.advantage_before
  have hfrozenLt :
      (grayChargedRunState q L a e n sigma A sm
        replay.advantageExitTime).core.frozen.length <
        grayChargedAdvantageRoundCount q := by
    rw [hcore]
    exact (grayChargedTailCertified_stateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm replay.advantageExitTime).frozen_bound.2
        (by rw [← hcore]; exact hactive)
  have hround : replay.advantageTerminal.frozen.length <
      grayTailBranch q L a e := by
    rw [replay.advantageTerminal_eq, hshape.1]
    exact lt_of_le_of_lt (by omega)
      (grayChargedAdvantageRoundCount_lt_grayTailBranch q L a e)
  have hslots : replay.advantageTerminal.slots =
      grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A replay.advantageTerminal.frozen
        (sm replay.advantageExitTime) := by
    rw [replay.advantageTerminal_eq]
    exact hshape.2
  have hinactive :
      ¬ GrayTailHasSon replay.advantageTerminal.slots z.1 z.2 := by
    intro hson
    rw [hslots] at hson
    have hunresolved := (grayTailHasSon_next_iff hround z.1 z.2).mp hson
    exact hsource.2 ⟨hunresolved.2.1, hunresolved.2.2⟩
  have hresolution :=
    grayChargedReplay_terminal_detailed_resolution replay z.1 z.2
      hsource.1 hinactive
  have hexit : GrayTailThresholdExit e A sm
      replay.advantageTerminal.frozen z.1 z.2 := by
    rcases hresolution with h | h
    · exact h.2
    · exact h.1.toThresholdExit
  obtain ⟨k, hk⟩ := hexit.ownerSplitAt
  exact ⟨{
    source_lt := hsource.1
    inactive := hinactive
    resolution := hresolution
    ownerIndex := k
    ownerSplit := hk }⟩

/-- The aggregate arithmetic behind the charge transport.

`m` coarse sources are split (up to a three quarters count) into `m1` raised sources
and `m2` server resolved sources.  The displayed aggregate `Q` is split into the part
`Qcalls` that is transported into recursive calls and the residual extra request `R`,
which is bounded by the raised sources at the fine scale `eps / (6 * kappa)`.
Under those hypotheses the recursive mass `Mrec` plus the reserve mass `Mres`
dominates both `(kappa + 1/2) * Q` and the coarse budget `Nalpha = m * eps`. -/
theorem grayCharged_aggregate_bounds
    {m m1 m2 : Nat}
    {kappa eps alphaCall Q Qcalls R Mrec Mres Nalpha : Rat}
    (hkappa : 1 <= kappa) (heps : 0 < eps)
    (hm : (m : Rat) * eps = Nalpha)
    (hcount : 3 * (m : Rat) <= 4 * ((m1 : Rat) + (m2 : Rat)))
    (hQupper : Q <= Nalpha)
    (hQlower : Nalpha / 2 <= Q)
    (hQsplit : Q = Qcalls + R)
    (hR : R <= (m1 : Rat) * (eps / (6 * kappa)))
    (hMrec : kappa * Qcalls <= Mrec)
    (hMres : (m1 : Rat) * eps + (m2 : Rat) * (eps - 4 * kappa * alphaCall)
      <= Mres)
    (hcall : alphaCall <= eps / (12 * kappa)) :
    (kappa + 1 / 2) * Q <= Mrec + Mres ∧ Nalpha <= Mrec + Mres := by
  have hkpos : (0 : Rat) < kappa := lt_of_lt_of_le one_pos hkappa
  have hm1 : (0 : Rat) <= (m1 : Rat) := Nat.cast_nonneg m1
  have hm2 : (0 : Rat) <= (m2 : Rat) := Nat.cast_nonneg m2
  have hmn : (0 : Rat) <= (m : Rat) := Nat.cast_nonneg m
  have hNa : 0 <= Nalpha := by rw [← hm]; positivity
  have hQnn : 0 <= Q := le_trans (by linarith) hQlower
  -- the call scale loses at most a third of a coarse unit
  have hcall' : 4 * kappa * alphaCall <= eps / 3 := by
    have h := mul_le_mul_of_nonneg_left hcall (by positivity : (0:Rat) <= 4 * kappa)
    calc 4 * kappa * alphaCall <= 4 * kappa * (eps / (12 * kappa)) := h
      _ = eps / 3 := by field_simp; ring
  -- the raised part dominates the amplified extra request
  have hkR : kappa * R <= (m1 : Rat) * eps / 6 := by
    have h := mul_le_mul_of_nonneg_left hR hkpos.le
    calc kappa * R <= kappa * ((m1 : Rat) * (eps / (6 * kappa))) := h
      _ = (m1 : Rat) * eps / 6 := by field_simp
  have hMres' : Nalpha / 2 + kappa * R <= Mres := by
    have hstep : (m1 : Rat) * eps + (m2 : Rat) * (2 * eps / 3) <=
        (m1 : Rat) * eps + (m2 : Rat) * (eps - 4 * kappa * alphaCall) := by
      have : 2 * eps / 3 <= eps - 4 * kappa * alphaCall := by linarith
      nlinarith
    have hbase : Nalpha / 2 + (m1 : Rat) * eps / 6 <=
        (m1 : Rat) * eps + (m2 : Rat) * (2 * eps / 3) := by
      rw [← hm]
      nlinarith [mul_le_mul_of_nonneg_right hcount heps.le]
    linarith
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ## Section 8.2: the displayed request at a raised source and one common
late service horizon

A source whose frozen son base has passed the controller threshold is
displayed at a full coarse unit for the rest of the run.  On the non-positive
branch such a request must eventually be served, which produces a genuine tail
family reserve at a finite service time.  Taking the maximum of `T + 1` and all
those finitely many service times gives the single late horizon `U` used by the
charge provenance, while the client display is unchanged by replay stability. -/

/-- The request the displayed family move puts on the son `c` of client `i` is the son request
computed from the frozen, slot and current entries. -/
lemma getFamilyReq_grayChargedTailFamilyMove_son {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (frozen : GrayTailFrozen n b) (slots : List (GrayTailSlot n b))
    (current : FamilyClientMove) (i : Fin n) (c : Fin b) :
    getFamilyReq
        (grayChargedTailFamilyMove source threshold eps frozen slots current)
        i.val [c.val] =
      grayChargedSonRequest source threshold eps
        (grayTailEntries frozen slots current) i c := by
  simp [getFamilyReq, familyClientMoveAt, grayChargedTailFamilyMove,
    List.getD_eq_getElem?_getD, c.isLt]

/-- Frozen round lists only grow, as prefixes, along the charged run. -/
lemma grayChargedStateAt_frozen_prefix_le
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) {t u : Nat} (htu : t <= u) :
    (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t).core.frozen <+:
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm u).core.frozen := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  clear htu
  induction d with
  | zero => simp
  | succ d ih =>
      refine ih.trans ?_
      have := grayChargedStateAt_succ_frozen_prefix
        (n := n) (b := b) q L a e sigma A sm (t + d)
      simpa [Nat.add_assoc] using this

end Kolmogorov
