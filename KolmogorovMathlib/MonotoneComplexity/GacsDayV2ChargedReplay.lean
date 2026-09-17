import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedController
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ShapeStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict

/-!
# Certification of the V2 charged controller (part 1: shapes and core)

Strict mirror of `GacsDayChargedReplay`'s certificate layer on the V2 block
records: the phase-tagged round shape (advantage block round on the
descending fine schedule, or one of the eight C1 spend block passes), the
phase-independent core certificate, and the projection from the certified
advantage tail.
-/

namespace Kolmogorov

/-- A slot of one V2 spend pass: its two-level coordinates lie in the pass's
spare-pair block. -/
def GrayChargedBlockSpendSlotV2 (n b source L pass : Nat)
    (s : GrayTailSlot n b) : Prop :=
  (s.2.1, s.2.2) ∈ grayBlockSpendPairs b source L pass

/-- The shape of one frozen V2 charged round: either an advantage round, whose block anchor and fine
end are the round's `grayTailRoundEps`/`grayTailRoundDelta`, whose move passes
`grayChargedBlockGoalAtB`, whose slots lie in the advantage block of its index and above sources
below `grayChargedSourceCount a e`, and whose index is below `grayChargedAdvantageRoundCount q`;
or a spend round of some pass `< 8`, with the pass anchors, a true
`grayChargedBlockSpendGoalAtB`, slots in the pass's spare-pair block, and a nonempty slot list. -/
def GrayChargedBlockRoundShapeV2 {n b : Nat}
    (q L a e : Nat) (sm : Nat -> FamilyServerMove)
    (p : GrayTailRoundV2 n b) : Prop :=
  (p.blockAnchor = grayTailRoundEps q L e p.roundIndex ∧
      p.fineEnd = grayTailRoundDelta q L e p.roundIndex ∧
      grayChargedBlockGoalAtB q L e p.roundIndex
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove p.fineEnd p.slots
            (sm p.serverTime)) = true ∧
      (forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val) ∧
      p.roundIndex < grayChargedAdvantageRoundCount q ∧
      (forall s, s ∈ p.slots ->
        s.2.1.val < grayChargedSourceCount a e)) ∨
    (∃ pass, pass < 8 ∧ p.blockAnchor = grayChargedSpendEps a L e pass ∧
      p.fineEnd = grayChargedSpendDelta a L e pass ∧
      grayChargedBlockSpendGoalAtB q L a e pass
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove p.fineEnd p.slots
            (sm p.serverTime)) = true ∧
      (∀ s ∈ p.slots, GrayChargedBlockSpendSlotV2 n b
        (grayChargedSourceCount a e) L pass s) ∧
      p.slots ≠ [])

/-- The phase-independent core certificate of a V2 charged state at time `t`: the recorded time is
`t`, the frozen rounds form a harvest chain over `A`, all frozen and open slots together are
pairwise distinct, every frozen round has index below the ledger length, a server time below
`t`, child bin `blockAnchor + graySpendSpan q`, the allocation list of its localised server
move, distinct slots and the shape `GrayChargedBlockRoundShapeV2`; the ledger is indexed in
order, chronological in server time, has no repeated son–grandson pair across rounds, and, when
`e = a + 8 * L + 3`, has non-overlapping scale windows. -/
structure GrayChargedCoreCertifiedV2 {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailStateV2 n b) : Prop where
  time_eq : st.time = t
  frozen_chain : GrayTailHarvestChainV2 n A sm st.frozen
  all_slots_nodup : (grayTailFrozenSlotsV2 st.frozen ++ st.slots).Nodup
  round_valid : forall p, p ∈ st.frozen ->
    p.roundIndex < st.frozen.length ∧
    p.serverTime < t ∧
    p.childEps = p.blockAnchor + graySpendSpan q ∧
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove p.fineEnd p.slots
          (sm p.serverTime)) ∧
    p.slots.Nodup ∧
    GrayChargedBlockRoundShapeV2 q L a e sm p
  frozen_index : forall k, forall hk : k < st.frozen.length,
    (st.frozen[k]'hk).roundIndex = k
  frozen_chrono : forall i j, forall hi : i < st.frozen.length,
    forall hj : j < st.frozen.length, i < j ->
      (st.frozen[i]'hi).serverTime < (st.frozen[j]'hj).serverTime
  frozen_cross_pairs : forall p, p ∈ st.frozen -> forall r, r ∈ st.frozen ->
    p.roundIndex < r.roundIndex ->
    forall sl, sl ∈ p.slots -> forall sl2, sl2 ∈ r.slots ->
      (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2)
  frozen_window_order : e = a + 8 * L + 3 ->
    forall p, p ∈ st.frozen -> forall r, r ∈ st.frozen ->
    p.roundIndex < r.roundIndex -> r.fineEnd <= p.blockAnchor

/-- The append nodup of the strict advantage shape (cross-round grandsons in
disjoint block ranges; current block beyond every frozen one). -/
lemma grayBlockTailShapeV2_allSlots_nodup {n b : Nat} {q L : Nat}
    {st : GrayTailStateV2 n b}
    (hshape : GrayBlockTailShapeV2 q L st) :
    (grayTailFrozenSlotsV2 st.frozen ++ st.slots).Nodup := by
  rw [List.nodup_append]
  refine ⟨hshape.frozen_nodup, hshape.slots_nodup, ?_⟩
  intro s hsf s2 hss heq
  subst heq
  rw [grayTailFrozenSlotsV2, List.mem_flatMap] at hsf
  obtain ⟨p, hp, hsp⟩ := hsf
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hfr := hshape.frozen_round_range k hk s hsp
  have hcur := hshape.slots_range s hss
  exact grayInAdvBlock_ne_of_round_ne hfr hcur (by omega) rfl

/-- Projection: the certified strict advantage tail plus the source invariant
yields the V2 charged core certificate. -/
lemma GrayChargedBlockTailCertifiedV2.toCore {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
    (hsource : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) st) :
    GrayChargedCoreCertifiedV2 q L a e A sm t st := by
  refine ⟨hst.time_eq, hst.frozen_chain,
    grayBlockTailShapeV2_allSlots_nodup hst.shape, ?_,
    hst.frozen_index, hst.frozen_chrono, ?_, ?_⟩
  · intro p hp
    rcases hst.round_valid p hp with
      ⟨hindex, hanchor, hchild, hfine, htime, halloc, hgoal, hnodup, hround⟩
    refine ⟨hindex, htime, hchild, halloc, hnodup, ?_⟩
    exact Or.inl ⟨hanchor, hfine, hgoal, hround,
      lt_of_lt_of_le hindex hst.frozen_bound.1,
      fun s hs => hsource.frozen p hp s hs⟩
  · intro p hp r hr hidx sl hsl sl2 hsl2 heq
    have hpB := (hst.round_valid p hp).2.2.2.2.2.2.2.2 sl hsl
    have hrB := (hst.round_valid r hr).2.2.2.2.2.2.2.2 sl2 hsl2
    exact grayInAdvBlock_ne_of_round_ne hpB hrB (Nat.ne_of_lt hidx)
      (congrArg (fun z => z.2.val) heq)
  · intro _ p hp r hr hidx
    have hpA := (hst.round_valid p hp).2.1
    have hrF := (hst.round_valid r hr).2.2.2.1
    have hpRC : p.roundIndex < grayChargedAdvantageRoundCount q :=
      lt_of_lt_of_le (hst.round_valid p hp).1 hst.frozen_bound.1
    have hrRC : r.roundIndex < grayChargedAdvantageRoundCount q :=
      lt_of_lt_of_le (hst.round_valid r hr).1 hst.frozen_bound.1
    rw [hpA, hrF]
    unfold grayTailRoundEps grayTailRoundDelta grayTailRoundEps
    have hRC8 : grayChargedAdvantageRoundCount q =
        grayTailRoundCount q - 8 := rfl
    have hco : (grayTailRoundCount q - 1 - r.roundIndex) + 1 <=
        grayTailRoundCount q - 1 - p.roundIndex := by omega
    calc grayCallDepth q e +
          (grayTailRoundCount q - 1 - r.roundIndex) * L + L
        = grayCallDepth q e +
          ((grayTailRoundCount q - 1 - r.roundIndex) + 1) * L := by ring
      _ <= grayCallDepth q e +
          (grayTailRoundCount q - 1 - p.roundIndex) * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_right L hco) _

/-- The V2 frozen slot layout: every frozen slot is a source slot or belongs
to an earlier spend pass's spare-pair block. -/
def GrayChargedFrozenLayoutV2 {n b : Nat}
    (source L pass : Nat) (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  forall s, s ∈ grayTailFrozenSlotsV2 frozen ->
    s.2.1.val < source ∨
      ∃ oldPass, oldPass < pass ∧
        GrayChargedBlockSpendSlotV2 n b source L oldPass s

/-- The certificate of a V2 charged state in a spend pass: the core certificate, together with the
snapshot datum that the unavailable list is `A` plus the harvest of the pass's slots at a server
time before the state's own time and after the exchange of every frozen round (for pass 0 the
raised-service wait exit, for later passes the previous freeze). -/
structure GrayChargedSpendCertifiedV2 {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t pass : Nat) (st : GrayTailStateV2 n b) : Prop where
  core : GrayChargedCoreCertifiedV2 q L a e A sm t st
  pass_lt : pass < 8
  unavailable_snap : ∃ s, s < t ∧ (∀ p ∈ st.frozen, p.serverTime ≤ s) ∧
    st.unavailable =
      A ++ grayHarvest (grayChargedSpendDelta a L e pass) st.slots n (sm s)
  slots_eq : st.slots = grayChargedSlotsForPassV2 q L a e pass st.frozen
  slots_nonempty : st.slots.isEmpty = false
  done_false : st.done = false
  frozen_layout : GrayChargedFrozenLayoutV2
    (grayChargedSourceCount a e) L pass st.frozen
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q + pass

/-- The invariant of a V2 charged state in the done phase: the core invariant holds, no slots
are open, the done flag is set, the history is empty, and the frozen rounds have the eight-pass
layout and the corresponding length bound. -/
structure GrayChargedDoneCertifiedV2 {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove)
    (t : Nat) (st : GrayTailStateV2 n b) : Prop where
  core : GrayChargedCoreCertifiedV2 q L a e A sm t st
  slots_empty : st.slots = []
  done_true : st.done = true
  history_empty : st.history = ([], [])
  frozen_layout : GrayChargedFrozenLayoutV2
    (grayChargedSourceCount a e) L 8 st.frozen
  frozen_bound : st.frozen.length <= grayChargedAdvantageRoundCount q + 8

/-- The phase-indexed V2 certificate: an advantage state over an active core, a wait state carrying
the tag `.advantage` over a done core whose step only ticks the clock, a spend state satisfying
`GrayChargedSpendCertifiedV2`, and a done state satisfying `GrayChargedDoneCertifiedV2`. -/
inductive GrayChargedCertifiedV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedStateV2 n b -> Prop
  | advantage (st : GrayTailStateV2 n b)
      (hcore : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
      (hsource : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) st)
      (hdone : st.done = false) :
      GrayChargedCertifiedV2 q L a e sigma A sm t
        { phase := .advantage, core := st }
  | wait (st : GrayTailStateV2 n b)
      (hcore : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
      (hsource : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) st)
      (hdone : st.done = true) :
      GrayChargedCertifiedV2 q L a e sigma A sm t
        { phase := .advantage, core := st }
  | spend (pass : Nat) (st : GrayTailStateV2 n b)
      (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass st) :
      GrayChargedCertifiedV2 q L a e sigma A sm t
        { phase := .spend pass, core := st }
  | done (st : GrayTailStateV2 n b)
      (hdone : GrayChargedDoneCertifiedV2 q L a e A sm t st) :
      GrayChargedCertifiedV2 q L a e sigma A sm t
        { phase := .done, core := st }

/-- The initial V2 charged state is certified (advantage phase). -/
lemma grayChargedCertifiedV2_initial {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayChargedCertifiedV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm 0
      (grayChargedInitialStateV2 n (grayTailBranch q L a e) a e q L A) := by
  refine GrayChargedCertifiedV2.advantage _ ?_ ?_ rfl
  · exact grayChargedBlockTailCertifiedV2_initial q L a e A sm
  · constructor
    · intro s hs
      have := grayAdvBlockSlots_mem hs
      exact this.1
    · intro p hp
      simp [grayChargedBlockTailInitialStateV2] at hp

/-- Slots of a source-invariant V2 frozen ledger stay in the source region. -/
lemma grayChargedFrozenSlotsV2_source {n b used : Nat}
    {st : GrayTailStateV2 n b} (hst : GrayTailSourceInvariantV2 used st) :
    forall s, s ∈ grayTailFrozenSlotsV2 st.frozen -> s.2.1.val < used := by
  intro s hs
  rw [grayTailFrozenSlotsV2, List.mem_flatMap] at hs
  obtain ⟨p, hp, hsp⟩ := hs
  exact hst.frozen p hp s hsp

/-- A certified V2 core stays certified when its slots are replaced by any distinct list disjoint
from the frozen slots and its history is reset. -/
lemma GrayChargedCoreCertifiedV2.withSlots {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (done : Bool) (slots : List (GrayTailSlot n b))
    (hslots : slots.Nodup)
    (hdisjoint : (grayTailFrozenSlotsV2 st.frozen).Disjoint slots) :
    GrayChargedCoreCertifiedV2 q L a e A sm t
      { st with done := done, slots := slots, history := ([], []) } := by
  refine ⟨hst.time_eq, hst.frozen_chain, ?_, ?_, hst.frozen_index,
    hst.frozen_chrono, hst.frozen_cross_pairs, hst.frozen_window_order⟩
  · rw [List.nodup_append]
    exact ⟨(List.nodup_append.mp hst.all_slots_nodup).1,
      hslots, List.disjoint_iff_ne.mp hdisjoint⟩
  · intro p hp
    exact hst.round_valid p hp

/-- The same replacement of slots, with the unavailable allocation replaced as well. -/
lemma GrayChargedCoreCertifiedV2.withSlotsUnavailable {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (done : Bool) (slots : List (GrayTailSlot n b))
    (hslots : slots.Nodup)
    (hdisjoint : (grayTailFrozenSlotsV2 st.frozen).Disjoint slots)
    (unavailable' : Allocation) :
    GrayChargedCoreCertifiedV2 q L a e A sm t
      { st with
        done := done
        slots := slots
        history := ([], [])
        unavailable := unavailable' } := by
  refine ⟨hst.time_eq, hst.frozen_chain, ?_, ?_, hst.frozen_index,
    hst.frozen_chrono, hst.frozen_cross_pairs, hst.frozen_window_order⟩
  · rw [List.nodup_append]
    exact ⟨(List.nodup_append.mp hst.all_slots_nodup).1,
      hslots, List.disjoint_iff_ne.mp hdisjoint⟩
  · intro p hp
    exact hst.round_valid p hp

/-- The same replacement of slots and unavailable allocation, with the round start
reset as well. -/
lemma GrayChargedCoreCertifiedV2.withSlotsUnavailableStart {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (done : Bool) (roundStart : Nat) (slots : List (GrayTailSlot n b))
    (hslots : slots.Nodup)
    (hdisjoint : (grayTailFrozenSlotsV2 st.frozen).Disjoint slots)
    (unavailable' : Allocation) :
    GrayChargedCoreCertifiedV2 q L a e A sm t
      { st with
        done := done
        roundStart := roundStart
        slots := slots
        history := ([], [])
        unavailable := unavailable' } := by
  refine ⟨hst.time_eq, hst.frozen_chain, ?_, ?_, hst.frozen_index,
    hst.frozen_chrono, hst.frozen_cross_pairs, hst.frozen_window_order⟩
  · rw [List.nodup_append]
    exact ⟨(List.nodup_append.mp hst.all_slots_nodup).1,
      hslots, List.disjoint_iff_ne.mp hdisjoint⟩
  · intro p hp
    exact hst.round_valid p hp

/-- Under the V2 source invariant the frozen rounds satisfy the layout condition of every pass. -/
lemma grayCharged_source_frozen_layout_v2 {n b source L pass : Nat}
    {st : GrayTailStateV2 n b} (hst : GrayTailSourceInvariantV2 source st) :
    GrayChargedFrozenLayoutV2 source L pass st.frozen := by
  intro s hs
  left
  exact grayChargedFrozenSlotsV2_source hst s hs

/-- A certified V2 core stays certified at time `t + 1` after a tick that only changes the time,
round start, done flag and history. -/
lemma GrayChargedCoreCertifiedV2.tick {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (roundStart : Nat) (done : Bool) (history : FamilyGameHistory) :
    GrayChargedCoreCertifiedV2 q L a e A sm (t + 1)
      { st with
        time := st.time + 1
        roundStart := roundStart
        done := done
        history := history } := by
  refine ⟨congrArg (fun u => u + 1) hst.time_eq, hst.frozen_chain,
    hst.all_slots_nodup, ?_, hst.frozen_index, hst.frozen_chrono,
    hst.frozen_cross_pairs, hst.frozen_window_order⟩
  intro p hp
  rcases hst.round_valid p hp with
    ⟨hindex, htime, hchild, halloc, hnodup, hphase⟩
  exact ⟨hindex, by omega, hchild, halloc, hnodup, hphase⟩

/-- Every slot delivered for a V2 pass is a pass-tagged block spare slot. -/
lemma grayChargedSlotsForPassV2_spendSlot {n b : Nat}
    {q L a e pass : Nat} {frozen : List (GrayTailRoundV2 n b)}
    {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSlotsForPassV2 q L a e pass frozen) :
    GrayChargedBlockSpendSlotV2 n b (grayChargedSourceCount a e) L pass s := by
  unfold grayChargedSlotsForPassV2 at hs
  exact grayBlockSpendSlotsV2_pair hs

/-- A just-finished V2 advantage phase records its last round at the
transition time. -/
lemma grayChargedBlockTailStepV2_done_getLast {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hslots : st.slots.isEmpty = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A st m).done = true) :
    Option.map GrayTailRoundV2.serverTime
        (grayChargedBlockTailStepV2 q L a e sigma A st m).frozen.getLast? =
      some st.time := by
  by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
      st.slots.length st.unavailable
      (grayBlockCurrentMoveV2 q L e sigma st)
      (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
        st.slots m) = true
  · simp only [grayChargedBlockTailStepV2, hactive, hslots,
      Bool.false_eq_true, ↓reduceIte, hg, List.getLast?_concat,
      Option.map_some]
  · exfalso
    simp only [grayChargedBlockTailStepV2, hactive, hslots,
      Bool.false_eq_true, ↓reduceIte, hg] at hdone

/-- The V2 advantage-to-spend transition is certified: the pass-0 harvest is
taken at a server time `s` after every frozen round's exchange (the wait
exit). -/
lemma grayChargedStartSpendV2_certified {n q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n (grayTailBranch q L a e)}
    {m : FamilyServerMove}
    (hcert : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
    (hsource : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) st)
    (hm : ∃ s, s < t ∧ (∀ p ∈ st.frozen, p.serverTime ≤ s) ∧ m = sm s) :
    GrayChargedCertifiedV2 q L a e sigma A sm t
      (grayChargedStartSpendV2 q L a e A st m) := by
  obtain ⟨s, hst, hfr, rfl⟩ := hm
  let slots := grayChargedSlotsForPassV2 q L a e 0 st.frozen
  have hslotsNodup : slots.Nodup := by
    dsimp [slots, grayChargedSlotsForPassV2]
    exact grayBlockSpendSlotsV2_nodup _ _ _ _ _ _ _
  have hdisjoint : (grayTailFrozenSlotsV2 st.frozen).Disjoint slots := by
    dsimp [slots, grayChargedSlotsForPassV2]
    exact grayBlockSource_disjoint_spendV2
      (grayChargedFrozenSlotsV2_source hsource)
  have hcore := (hcert.toCore (a := a) hsource).withSlots false slots
    hslotsNodup hdisjoint
  have hlayout := grayCharged_source_frozen_layout_v2
    (L := L) (pass := 0) hsource
  change GrayChargedCertifiedV2 q L a e sigma A sm t
    (if slots.isEmpty then
      { phase := .done
        core := { st with done := true, slots := [], history := ([], []) } }
    else
      { phase := .spend 0
        core := { st with
          done := false
          roundStart := st.time
          slots := slots
          history := ([], [])
          unavailable := A ++
            grayHarvest (grayChargedSpendDelta a L e 0) slots n (sm s) } })
  by_cases hempty : slots.isEmpty = true
  · rw [if_pos hempty]
    apply GrayChargedCertifiedV2.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hcert.toCore (a := a) hsource).withSlots true
        ([] : List (GrayTailSlot n (grayTailBranch q L a e)))
        List.nodup_nil (List.disjoint_nil_right _)
    · rfl
    · rfl
    · rfl
    · exact grayCharged_source_frozen_layout_v2 (st := st) (L := L) (pass := 8) hsource
    · exact le_trans hcert.frozen_bound.1 (by omega)
  · have hnonempty : slots.isEmpty = false := by
      cases h : slots.isEmpty <;> simp_all
    rw [if_neg (by simpa using hnonempty)]
    apply GrayChargedCertifiedV2.spend 0
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hcert.toCore (a := a) hsource).withSlotsUnavailableStart false st.time
        slots hslotsNodup hdisjoint _
    · exact ⟨s, hst, hfr, rfl⟩
    · rfl
    · exact hnonempty
    · rfl
    · exact hlayout
    · exact hcert.frozen_bound.1

/-- Freezing one more V2 round appends that round's slots to the frozen slots. -/
lemma grayTailFrozenSlotsV2_append {n b : Nat}
    (frozen : List (GrayTailRoundV2 n b)) (p : GrayTailRoundV2 n b) :
    grayTailFrozenSlotsV2 (frozen ++ [p]) =
      grayTailFrozenSlotsV2 frozen ++ p.slots := by
  simp [grayTailFrozenSlotsV2]

/-- Cross-round pair disjointness when appending a frozen spend round. -/
private lemma grayChargedCoreCertifiedV2_freezeSpend_cross {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    {p : GrayTailRoundV2 n b}
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpSpendSlots : ∀ s ∈ p.slots, GrayChargedBlockSpendSlotV2 n b
      (grayChargedSourceCount a e) L pass s)
    (hlayout : GrayChargedFrozenLayoutV2
      (grayChargedSourceCount a e) L pass st.frozen) :
    forall r0, r0 ∈ st.frozen ++ [p] ->
    forall r1, r1 ∈ st.frozen ++ [p] ->
    r0.roundIndex < r1.roundIndex ->
    forall sl, sl ∈ r0.slots -> forall sl2, sl2 ∈ r1.slots ->
      (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2) := by
  intro r0 hr0 r1 hr1 hidx sl hsl sl2 hsl2 heq
  rcases List.mem_append.mp hr0 with hr0in | hr0 <;>
    rcases List.mem_append.mp hr1 with hr1in | hr1
  · exact hst.frozen_cross_pairs r0 hr0in r1 hr1in hidx sl hsl sl2 hsl2 heq
  · have hr1p : r1 = p := by simpa using hr1
    subst hr1p
    have hlay := hlayout sl (by
      rw [grayTailFrozenSlotsV2, List.mem_flatMap]; exact ⟨r0, hr0in, hsl⟩)
    have hnew := hpSpendSlots sl2 hsl2
    rcases hlay with hsrc | ⟨oldPass, holdlt, holdslot⟩
    · have hge : grayChargedSourceCount a e <= sl2.2.1.val := grayBlockSpendPairs_first_ge hnew
      have h1 : sl.2.1.val = sl2.2.1.val := congrArg (fun z => z.1.val) heq
      omega
    · have hdisj := grayBlockSpendPairs_disjoint
        (b := b) (source := grayChargedSourceCount a e) (L := L) holdlt
      rw [List.disjoint_iff_ne] at hdisj
      exact hdisj (sl.2.1, sl.2.2) holdslot (sl2.2.1, sl2.2.2) hnew heq
  · have hr0p : r0 = p := by simpa using hr0
    have hidx1 := (hst.round_valid r1 hr1in).1
    rw [hr0p, hpIndex] at hidx; omega
  · have hr0p : r0 = p := by simpa using hr0
    have hr1p : r1 = p := by simpa using hr1
    rw [hr0p, hr1p] at hidx; omega

/-- Window ordering of frozen rounds when appending a frozen spend round. -/
private lemma grayChargedCoreCertifiedV2_freezeSpend_window_order
    {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    {p : GrayTailRoundV2 n b}
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpass : pass < 8)
    (hpFine : p.fineEnd = grayChargedSpendDelta a L e pass)
    (hlayout : GrayChargedFrozenLayoutV2
      (grayChargedSourceCount a e) L pass st.frozen) :
    e = a + 8 * L + 3 ->
    forall r0, r0 ∈ st.frozen ++ [p] ->
    forall r1, r1 ∈ st.frozen ++ [p] ->
    r0.roundIndex < r1.roundIndex -> r1.fineEnd <= r0.blockAnchor := by
  intro hpin r0 hr0 r1 hr1 hidx
  rcases List.mem_append.mp hr0 with hr0in | hr0 <;>
    rcases List.mem_append.mp hr1 with hr1in | hr1
  · exact hst.frozen_window_order hpin r0 hr0in r1 hr1in hidx
  · have hr1p : r1 = p := by simpa using hr1
    have hnewFine : r1.fineEnd = grayChargedSpendDelta a L e pass := by rw [hr1p, hpFine]
    have hnewLe : r1.fineEnd <= e := by
      rw [hnewFine, grayChargedSpendDelta, hpin, grayChargedSpendEps_pinned_eq hpass]
      have hle : (7 - pass) * L + L <= 8 * L := by
        have : (7 - pass) + 1 <= 8 := by omega
        calc (7 - pass) * L + L = ((7 - pass) + 1) * L := by ring
          _ <= 8 * L := Nat.mul_le_mul_right L this
      omega
    rcases (hst.round_valid r0 hr0in).2.2.2.2.2 with ⟨h0A, -⟩ |
      ⟨p0, hp0, h0A, -, -, h0Slots, h0Ne⟩
    · rw [h0A]; refine le_trans hnewLe ?_; unfold grayTailRoundEps
      have hce : e <= grayCallDepth q e := by unfold grayCallDepth; omega
      omega
    · obtain ⟨sl, hsl⟩ := List.exists_mem_of_ne_nil _ h0Ne
      have hlay := hlayout sl (by
        rw [grayTailFrozenSlotsV2, List.mem_flatMap]; exact ⟨r0, hr0in, hsl⟩)
      have hp0pair := h0Slots sl hsl
      rcases hlay with hsrc | ⟨oldPass, holdlt, holdslot⟩
      · exfalso; have hge : grayChargedSourceCount a e <= sl.2.1.val :=
          grayBlockSpendPairs_first_ge hp0pair
        omega
      · have hpe : p0 = oldPass := grayBlockSpendPairs_pass_eq hp0pair holdslot
        have hp0lt : p0 < pass := by omega
        rw [h0A, hnewFine, grayChargedSpendDelta, hpin, grayChargedSpendEps_pinned_eq hpass,
          grayChargedSpendEps_pinned_eq (by omega : p0 < 8)]
        have hle : (7 - pass) * L + L <= (7 - p0) * L := by
          have : (7 - pass) + 1 <= 7 - p0 := by omega
          calc (7 - pass) * L + L = ((7 - pass) + 1) * L := by ring
            _ <= (7 - p0) * L := Nat.mul_le_mul_right L this
        omega
  · exfalso; have hr0p : r0 = p := by simpa using hr0
    have hidx1 := (hst.round_valid r1 hr1in).1
    rw [hr0p, hpIndex] at hidx; omega
  · exfalso; have hr0p : r0 = p := by simpa using hr0
    have hr1p : r1 = p := by simpa using hr1
    rw [hr0p, hr1p] at hidx; omega

/-- Freeze one accepted V2 spend block round. -/
lemma GrayChargedCoreCertifiedV2.freezeSpend {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hst : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (p : GrayTailRoundV2 n b)
    (hpSlots : p.slots = st.slots)
    (hpIndex : p.roundIndex = st.frozen.length)
    (hpTime : p.serverTime = t)
    (hpass : pass < 8)
    (hpDepth : p.blockAnchor = grayChargedSpendEps a L e pass)
    (hpChild : p.childEps = p.blockAnchor + graySpendSpan q)
    (hpFine : p.fineEnd = grayChargedSpendDelta a L e pass)
    (hpAllocated : p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove p.fineEnd p.slots
          (sm p.serverTime)))
    (s : Option Nat)
    (hs : GrayTailSnapOKV2 st.frozen p s)
    (hpSnap : p.unavailable =
      A ++ grayHarvest p.fineEnd p.slots n (grayHarvestSnapshot sm s))
    (hpGoal : grayChargedBlockSpendGoalAtB q L a e pass
      p.slots.length p.unavailable p.move
        (grayTailLocalServerMove p.fineEnd p.slots
          (sm p.serverTime)) = true)
    (hpSpendSlots : ∀ s ∈ p.slots, GrayChargedBlockSpendSlotV2 n b
      (grayChargedSourceCount a e) L pass s)
    (hpNe : p.slots ≠ [])
    (hlayout : GrayChargedFrozenLayoutV2
      (grayChargedSourceCount a e) L pass st.frozen)
    (unavailable' : Allocation) :
    GrayChargedCoreCertifiedV2 q L a e A sm (t + 1)
      { time := st.time + 1
        roundStart := st.time + 1
        done := false
        frozen := st.frozen ++ [p]
        unavailable := unavailable'
        slots := []
        anchoringSlots := []
        history := ([], []) } := by
  have hcross := grayChargedCoreCertifiedV2_freezeSpend_cross hst hpIndex hpSpendSlots hlayout
  have hwin := grayChargedCoreCertifiedV2_freezeSpend_window_order hst hpIndex hpass hpFine hlayout
  refine ⟨congrArg (fun u => u + 1) hst.time_eq, ?_, ?_, ?_, ?_, ?_, hcross, hwin⟩
  · exact grayTailHarvestChainV2_append hst.frozen_chain hs hpSnap
  · simpa [grayTailFrozenSlotsV2_append, hpSlots] using hst.all_slots_nodup
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hst.round_valid r hr with
        ⟨hindex, htime, hchild, halloc, hnodup, hphase⟩
      refine ⟨?_, ?_, hchild, halloc, hnodup, hphase⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
    · have hrp : r = p := by simpa using hr
      subst r
      refine ⟨?_, ?_, hpChild, hpAllocated, ?_,
        Or.inr ⟨pass, hpass, hpDepth, hpFine, hpGoal, hpSpendSlots, hpNe⟩⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · omega
      · rw [hpSlots]; exact (List.nodup_append.mp hst.all_slots_nodup).2.1
  · intro k hk
    have hklen : k < st.frozen.length + 1 := by simpa using hk
    by_cases hkf : k < st.frozen.length
    · rw [List.getElem_append_left hkf]; exact hst.frozen_index k hkf
    · have hke : k = st.frozen.length := by omega
      subst hke
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hk = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hgetp, hpIndex]
  · intro i j hi hj hij
    have hjlen : j < st.frozen.length + 1 := by simpa using hj
    by_cases hjf : j < st.frozen.length
    · have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif, List.getElem_append_left hjf]
      exact hst.frozen_chrono i j hif hjf hij
    · have hje : j = st.frozen.length := by omega
      subst hje
      have hif : i < st.frozen.length := by omega
      rw [List.getElem_append_left hif]
      have hgetp : (st.frozen ++ [p])[st.frozen.length]'hj = p := by
        rw [List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hgetp, hpTime]
      have hmem : st.frozen[i]'hif ∈ st.frozen := List.getElem_mem hif
      exact (hst.round_valid _ hmem).2.1

/-- The V2 frozen layout condition weakens as the pass index grows. -/
lemma GrayChargedFrozenLayoutV2.mono {n b source L pass pass' : Nat}
    {frozen : List (GrayTailRoundV2 n b)}
    (h : GrayChargedFrozenLayoutV2 source L pass frozen)
    (hle : pass <= pass') :
    GrayChargedFrozenLayoutV2 source L pass' frozen := by
  intro s hs
  rcases h s hs with hs | ⟨oldPass, hold, hslot⟩
  · exact Or.inl hs
  · exact Or.inr ⟨oldPass, lt_of_lt_of_le hold hle, hslot⟩

/-- Freezing a V2 round whose slots belong to pass `pass` yields the layout of pass `pass + 1`. -/
lemma grayChargedFrozenLayoutV2_append {n b source L pass : Nat}
    {frozen : List (GrayTailRoundV2 n b)} {p : GrayTailRoundV2 n b}
    (hlayout : GrayChargedFrozenLayoutV2 source L pass frozen)
    (hp : forall s, s ∈ p.slots ->
      GrayChargedBlockSpendSlotV2 n b source L pass s) :
    GrayChargedFrozenLayoutV2 source L (pass + 1) (frozen ++ [p]) := by
  intro s hs
  rw [grayTailFrozenSlotsV2_append] at hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases hlayout s hs with hs | ⟨oldPass, hold, hslot⟩
    · exact Or.inl hs
    · exact Or.inr ⟨oldPass, by omega, hslot⟩
  · exact Or.inr ⟨pass, by omega, hp s hs⟩

/-- Under the V2 layout of pass `pass`, the frozen slots are disjoint from the slots that pass
opens. -/
lemma grayChargedFrozenLayoutV2_disjoint_current {n b source L pass : Nat}
    {frozen : List (GrayTailRoundV2 n b)}
    {frozen' : GrayTailFrozen n b}
    {threshold eps alpha : Rat}
    (hlayout : GrayChargedFrozenLayoutV2 source L pass frozen) :
    (grayTailFrozenSlotsV2 frozen).Disjoint
      (grayBlockSpendSlotsV2 source L pass threshold eps alpha frozen') := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  rcases hlayout s hs with hsource | ⟨oldPass, hold, hslot⟩
  · have hge := grayBlockSpendSlotsV2_son_ge ht
    rw [heq] at hsource
    omega
  · have htSlot := grayBlockSpendSlotsV2_pair ht
    have hdisj := grayBlockSpendPairs_disjoint
      (b := b) (source := source) (L := L) hold
    rw [List.disjoint_iff_ne] at hdisj
    exact hdisj (s.2.1, s.2.2) hslot (t.2.1, t.2.2) htSlot
      (congrArg Prod.snd heq)

/-- Freezing the round of a certified V2 spend pass yields the layout of the next pass. -/
lemma grayChargedSpendLayoutV2_advance {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b} {p : GrayTailRoundV2 n b}
    (hst : GrayChargedSpendCertifiedV2 q L a e A sm t pass st)
    (hpSlots : p.slots = st.slots) :
    GrayChargedFrozenLayoutV2 (grayChargedSourceCount a e)
      L (pass + 1) (st.frozen ++ [p]) := by
  apply grayChargedFrozenLayoutV2_append hst.frozen_layout
  intro s hs
  rw [hpSlots, hst.slots_eq] at hs
  exact grayChargedSlotsForPassV2_spendSlot hs

/-- A certified V2 core stays certified when its slots are replaced by those of the next spend
pass. -/
lemma grayChargedCoreV2_with_next {n b q L a e t pass : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (hcore : GrayChargedCoreCertifiedV2 q L a e A sm t st)
    (hlayout : GrayChargedFrozenLayoutV2
      (grayChargedSourceCount a e) L pass st.frozen)
    (_hpass : pass < 8) :
    GrayChargedCoreCertifiedV2 q L a e A sm t
      { st with
        done := false
        slots := grayChargedSlotsForPassV2 q L a e pass st.frozen
        history := ([], []) } := by
  apply hcore.withSlots
  · dsimp [grayChargedSlotsForPassV2]
    exact grayBlockSpendSlotsV2_nodup _ _ _ _ _ _ _
  · dsimp [grayChargedSlotsForPassV2]
    exact grayChargedFrozenLayoutV2_disjoint_current hlayout

/-- **The step from a certified terminal advantage core** (v15.1 A3): when
every raised son is served the controller starts the spend phase with the
pass-0 harvest taken now; otherwise it waits (the phase tag stays
`.advantage` over the done core). -/
lemma grayChargedCertifiedV2_step_of_terminal {n q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {core : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hnext : GrayChargedBlockTailCertifiedV2 q L e A sm (t + 1)
      (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)))
    (hsourceNext : GrayTailSourceInvariantV2 (grayChargedSourceCount a e)
      (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)))
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done =
      true) :
    GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
      (grayChargedStepV2 q L a e sigma A
        { phase := .advantage, core := core } (sm t)) := by
  have hphase : ({ phase := .advantage, core := core } :
      GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
  by_cases hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
  · rw [grayChargedStepV2_advantage_exit q L a e sigma A
      { phase := .advantage, core := core } (sm t) hphase hdone hserved]
    have hfr : ∀ p ∈ (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).frozen,
        p.serverTime ≤ t := by
      intro p hp
      exact Nat.lt_succ_iff.mp (hnext.round_valid p hp).2.2.2.2.1
    exact grayChargedStartSpendV2_certified (sigma := sigma) hnext hsourceNext
      ⟨t, Nat.lt_succ_self t, hfr, rfl⟩
  · have hserved' : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) =
          false := by
      simpa using hserved
    rw [grayChargedStepV2_advantage_wait q L a e sigma A
      { phase := .advantage, core := core } (sm t) hphase hdone hserved']
    exact GrayChargedCertifiedV2.wait _ hnext hsourceNext hdone

/-- Step certification for a V2 spend phase state when the goal is achieved. -/
private lemma grayChargedCertifiedV2_step_spend_freeze {n q L a e t pass : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {core : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass core)
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length core.unavailable
      (grayBlockSpendMoveV2 q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) =
        true) :
    GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
      (grayChargedStepV2 q L a e sigma A { phase := .spend pass, core := core } (sm t)) := by
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  let epsRound := grayChargedSpendEps a L e pass
  let deltaRound := grayChargedSpendDelta a L e pass
  let current := grayBlockSpendMoveV2 q L a e pass sigma core
  let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
  let p : GrayTailRoundV2 n (grayTailBranch q L a e) :=
    { serverTime := core.time, roundIndex := core.frozen.length, blockAnchor := epsRound,
      childEps := epsRound + graySpendSpan q, fineEnd := deltaRound, slots := core.slots,
      move := current, allocated := grayTailLocalAllocatedList localSM,
      unavailable := core.unavailable }
  let frozen' := core.frozen ++ [p]
  let base : GrayTailStateV2 n (grayTailBranch q L a e) :=
    { time := core.time + 1, roundStart := core.time + 1, done := false, frozen := frozen',
      unavailable := A ++ grayHarvest (grayChargedSpendDelta a L e (pass + 1))
        (grayChargedSlotsForPassV2 q L a e (pass + 1) frozen') n (sm t),
      slots := [], anchoringSlots := [], history := ([], []) }
  have hpSlots : p.slots = core.slots := rfl
  have hfreeze : GrayChargedCoreCertifiedV2 q L a e A sm (t + 1) base := by
    dsimp [base, frozen']
    have hpIndex : p.roundIndex = core.frozen.length := rfl
    have hpTime : p.serverTime = t := hspend.core.time_eq
    have hpDepth : p.blockAnchor = grayChargedSpendEps a L e pass := rfl
    have hpChild : p.childEps = p.blockAnchor + graySpendSpan q := rfl
    have hpFine : p.fineEnd = grayChargedSpendDelta a L e pass := rfl
    have hpAllocated : p.allocated =
      grayTailLocalAllocatedList (grayTailLocalServerMove p.fineEnd p.slots (sm t)) := rfl
    have hpSnap : p.unavailable = core.unavailable := rfl
    have hpGoal : grayChargedBlockSpendGoalAtB q L a e pass p.slots.length p.unavailable p.move
      (grayTailLocalServerMove p.fineEnd p.slots (sm t)) = true := hgoal
    have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
    have hdeltaEq : grayChargedSpendDelta a L e pass = grayChargedSpendEps a L e pass + L := rfl
    obtain ⟨s0, hs0, hfr0, hsnap0⟩ := hspend.unavailable_snap
    have hsOK : GrayTailSnapOKV2 core.frozen p (some s0) := ⟨by simp, fun u hu => by
      have hus : u = s0 := by simpa using hu.symm
      subst hus; refine ⟨?_, hfr0⟩; rw [hpTime]; exact hs0⟩
    refine hspend.core.freezeSpend (pass := pass) p hpSlots hpIndex hpTime hspend.pass_lt
      hpDepth hpChild hpFine ?_ (some s0) hsOK ?_ ?_ ?_ ?_ hspend.frozen_layout _
    · simp [hpAllocated, hpFine, hpSlots, hpTime]
    · simpa [hpSnap, hpFine, hpSlots, grayHarvestSnapshot] using hsnap0
    · simpa [hpSnap, hpFine, hpSlots, hpDepth, hpTime, hdeltaEq, hspend.core.time_eq] using hpGoal
    · intro s hs; rw [hpSlots] at hs
      exact grayChargedSlotsForPassV2_spendSlot (by rw [<- hspend.slots_eq]; exact hs)
    · rw [hpSlots]; intro h; rw [h] at hslots; contradiction
  have hlayout : GrayChargedFrozenLayoutV2
      (grayChargedSourceCount a e) L (pass + 1) frozen' := by
    simpa [frozen'] using grayChargedSpendLayoutV2_advance hspend hpSlots
  by_cases hpass : pass + 1 < 8
  · let slots := grayChargedSlotsForPassV2 q L a e (pass + 1) frozen'
    by_cases hempty : slots.isEmpty = true
    · have hnil : slots = [] := List.isEmpty_iff.mp hempty
      have hslotsNil : grayChargedSlotsForPassV2 q L a e (pass + 1) frozen' = [] := by
        simpa [slots] using hnil
      let doneCore : GrayTailStateV2 n (grayTailBranch q L a e) := { base with done := true }
      have hcoreDone : GrayChargedCoreCertifiedV2 q L a e A sm (t + 1) doneCore := by
        have h := hfreeze.withSlots true [] (by simp) (by simp); simpa [doneCore, base] using h
      have hdoneCert : GrayChargedDoneCertifiedV2 q L a e A sm (t + 1) doneCore :=
        ⟨hcoreDone, rfl, rfl, rfl, hlayout.mono (by omega), by
          dsimp [doneCore, base, frozen']
          have hfb := hspend.frozen_bound
          rw [List.length_append, List.length_singleton]
          omega⟩
      have hout : GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
          { phase := .done, core := doneCore } := GrayChargedCertifiedV2.done doneCore hdoneCert
      simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound, current, localSM, p,
        frozen', base, slots, doneCore, hpass, hempty, hnil, hslotsNil] using hout
    · have hnempty : slots ≠ [] := by intro hnil; apply hempty; simp [hnil]
      have hslotsNe : grayChargedSlotsForPassV2 q L a e (pass + 1) frozen' ≠ [] := by
        simpa [slots] using hnempty
      let nextCore : GrayTailStateV2 n (grayTailBranch q L a e) := { base with slots := slots }
      have hcoreNext : GrayChargedCoreCertifiedV2 q L a e A sm (t + 1) nextCore := by
        have h := grayChargedCoreV2_with_next hfreeze hlayout hpass
        simpa [nextCore, slots, base] using h
      have hnonempty : slots.isEmpty = false := by cases h : slots.isEmpty <;> simp_all
      have hspendCert : GrayChargedSpendCertifiedV2 q L a e A sm (t + 1) (pass + 1) nextCore := by
        refine ⟨hcoreNext, hpass, ?_, ?_, ?_, ?_, hlayout, ?_⟩
        · refine ⟨t, by omega, ?_, ?_⟩
          · intro r hr
            change r ∈ core.frozen ++ [p] at hr
            rcases List.mem_append.mp hr with hr | hr
            · exact le_of_lt (hspend.core.round_valid r hr).2.1
            · have hrp : r = p := by simpa using hr
              subst hrp; change core.time ≤ t; rw [hspend.core.time_eq]
          · simp [nextCore, base, slots, frozen']
        · simp [nextCore, slots, base]
        · simpa [nextCore] using hnonempty
        · simp [nextCore, base]
        · dsimp [nextCore, slots, base, frozen']
          have hfb := hspend.frozen_bound
          rw [List.length_append, List.length_singleton]
          omega
      have hout : GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
          { phase := .spend (pass + 1), core := nextCore } :=
        GrayChargedCertifiedV2.spend (pass + 1) nextCore hspendCert
      simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound, current, localSM, p,
        frozen', base, slots, nextCore, hpass, hempty, hnempty, hslotsNe] using hout
  · have hpassLt := hspend.pass_lt
    have hpassEq : pass + 1 = 8 := by omega
    let doneCore : GrayTailStateV2 n (grayTailBranch q L a e) := { base with done := true }
    have hcoreDone : GrayChargedCoreCertifiedV2 q L a e A sm (t + 1) doneCore := by
      have h := hfreeze.withSlots true [] (by simp) (by simp); simpa [doneCore, base] using h
    have hdoneCert : GrayChargedDoneCertifiedV2 q L a e A sm (t + 1) doneCore :=
      ⟨hcoreDone, rfl, rfl, rfl, by simpa [hpassEq] using hlayout, by
        dsimp [doneCore, base, frozen']
        have hfb := hspend.frozen_bound
        rw [List.length_append, List.length_singleton]
        omega⟩
    have hout : GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
        { phase := .done, core := doneCore } := GrayChargedCertifiedV2.done doneCore hdoneCert
    simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound, current, localSM, p,
      frozen', base, doneCore, hpass, hspend.core.time_eq] using hout

/-- Step certification for a V2 spend phase state. -/
private lemma grayChargedCertifiedV2_step_spend {n q L a e t pass : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {core : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass core) :
    GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
      (grayChargedStepV2 q L a e sigma A { phase := .spend pass, core := core } (sm t)) := by
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  let epsRound := grayChargedSpendEps a L e pass
  let deltaRound := grayChargedSpendDelta a L e pass
  let current := grayBlockSpendMoveV2 q L a e pass sigma core
  let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
  by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length core.unavailable
      current localSM = true
  · exact grayChargedCertifiedV2_step_spend_freeze hspend hgoal
  · let nextCore : GrayTailStateV2 n (grayTailBranch q L a e) :=
      { core with
        time := core.time + 1
        history :=
          (core.history.1 ++ [current], core.history.2 ++ [localSM]) }
    have hcoreNext :
        GrayChargedCoreCertifiedV2 q L a e A sm (t + 1) nextCore := by
      simpa [nextCore] using
        hspend.core.tick core.roundStart core.done
          (core.history.1 ++ [current], core.history.2 ++ [localSM])
    have hspendCert : GrayChargedSpendCertifiedV2 q L a e A sm
        (t + 1) pass nextCore := by
      refine ⟨hcoreNext, hspend.pass_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨s0, hs0, hfr0, hsnap0⟩ := hspend.unavailable_snap
        exact ⟨s0, by omega, hfr0, by simpa [nextCore] using hsnap0⟩
      · simpa [nextCore] using hspend.slots_eq
      · simpa [nextCore] using hspend.slots_nonempty
      · simpa [nextCore] using hspend.done_false
      · simpa [nextCore] using hspend.frozen_layout
      · simpa [nextCore] using hspend.frozen_bound
    have hout : GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
        { phase := .spend pass, core := nextCore } :=
      GrayChargedCertifiedV2.spend pass nextCore hspendCert
    simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound,
      current, localSM, nextCore] using hout

/-- **Certification is preserved by the V2 charged step.** -/
lemma grayChargedCertifiedV2_step {n q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {st : GrayChargedStateV2 n (grayTailBranch q L a e)}
    (hst : GrayChargedCertifiedV2 q L a e sigma A sm t st) :
    GrayChargedCertifiedV2 q L a e sigma A sm (t + 1)
      (grayChargedStepV2 q L a e sigma A st (sm t)) := by
  cases hst with
  | advantage core hcore hsource hactive =>
      let next := grayChargedBlockTailStepV2 q L a e sigma A core (sm t)
      have hnext := grayChargedBlockTailCertifiedV2_step (a := a) sigma hcore
      have hsourceNext :=
        grayChargedBlockSourceInvariantV2_step q L a e sigma A core (sm t) hsource
      by_cases hdone : next.done = true
      · exact grayChargedCertifiedV2_step_of_terminal hnext hsourceNext hdone
      · have hnextActive : next.done = false := by cases h : next.done <;> simp_all
        simpa [grayChargedStepV2, next, hdone] using
          GrayChargedCertifiedV2.advantage next hnext hsourceNext hnextActive
  | wait core hcore hsource hdoneCore =>
      let next := grayChargedBlockTailStepV2 q L a e sigma A core (sm t)
      have hnext := grayChargedBlockTailCertifiedV2_step (a := a) sigma hcore
      have hsourceNext :=
        grayChargedBlockSourceInvariantV2_step q L a e sigma A core (sm t) hsource
      have hdone : next.done = true := by
        simp [next, grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
          hdoneCore, hdoneCore]
      exact grayChargedCertifiedV2_step_of_terminal hnext hsourceNext hdone
  | done core hdone =>
      apply GrayChargedCertifiedV2.done
      refine ⟨by simpa [grayChargedStepV2] using
          hdone.core.tick core.roundStart core.done core.history,
        by simpa [grayChargedStepV2] using hdone.slots_empty,
        by simpa [grayChargedStepV2] using hdone.done_true,
        by simpa [grayChargedStepV2] using hdone.history_empty,
        hdone.frozen_layout,
        by simpa [grayChargedStepV2] using hdone.frozen_bound⟩
  | spend pass core hspend =>
      exact grayChargedCertifiedV2_step_spend hspend

/-- Certification holds along the whole V2 charged run. -/
theorem grayChargedCertifiedV2_stateAt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedCertifiedV2 q L a e sigma A sm t
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedCertifiedV2_initial q L a e sigma A sm
  | succ t ih =>
      rw [grayChargedRunStateV2_succ]
      exact grayChargedCertifiedV2_step ih

end Kolmogorov
