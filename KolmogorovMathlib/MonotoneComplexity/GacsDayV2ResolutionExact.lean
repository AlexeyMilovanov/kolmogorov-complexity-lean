import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProgressBase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvSlots
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# The exact resolution invariant of the V2 block controller (Stage D2 input)

Mirror of `GacsDayChargedResolutionExact` on the V2 wide-block advantage
controller.  Every source fibre `(i, c)` is, at every stage: still active
with a fresh checkpoint, threshold-exited, or persistent-reserve-exited.
The wide slots carry fibre occupancy exactly like the narrow list (the
`HasSon` bridge), so the V1 fibre analysis ports through the `toV1`
projection.
-/

namespace Kolmogorov

/-- Fibre occupancy of the wide block equals that of the narrow list. -/
lemma grayBlockHasSon_iff {n b : Nat}
    {q L e used round : Nat} {threshold : Rat} {A : Allocation}
    {frozen : GrayTailFrozen n b} {sm : FamilyServerMove}
    (hr : round < b)
    (hG : (grayAdvBlockGrandsons b q L round) ≠ [])
    (i : Fin n) (c : Fin b) :
    GrayTailHasSon
        (grayBlockNextSlots q L e used round threshold A frozen sm) i c ↔
      GrayTailHasSon
        (grayTailNextSlots e used round threshold A frozen sm) i c := by
  constructor
  · rintro ⟨s, hs, hsi, hsc⟩
    rw [grayBlockNextSlots, List.mem_flatMap] at hs
    obtain ⟨i0, -, hs⟩ := hs
    rw [List.mem_flatMap] at hs
    obtain ⟨c0, hc0, hs⟩ := hs
    rw [List.mem_map] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    refine ⟨(i0, c0, ⟨round, hr⟩), ?_, hsi, hsc⟩
    rw [grayTailNextSlots, dif_pos hr, List.mem_flatMap]
    refine ⟨i0, List.mem_finRange _, ?_⟩
    rw [List.mem_map]
    exact ⟨c0, hc0, rfl⟩
  · rintro ⟨s, hs, hsi, hsc⟩
    rw [grayTailNextSlots, dif_pos hr, List.mem_flatMap] at hs
    obtain ⟨i0, -, hs⟩ := hs
    rw [List.mem_map] at hs
    obtain ⟨c0, hc0, rfl⟩ := hs
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hG
    refine ⟨(i0, c0, g), ?_, hsi, hsc⟩
    rw [grayBlockNextSlots, List.mem_flatMap]
    refine ⟨i0, List.mem_finRange _, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨c0, hc0, ?_⟩
    rw [List.mem_map]
    exact ⟨g, hg, rfl⟩

/-- Every son `c` with `c.val < 2 ^ (e - a)` of every root is in exactly one of three states on the
V1 projection of the frozen ledger: open with a fresh checkpoint, closed above the exit
threshold with a threshold exit, or closed with a persistent reserve exit at or below that
threshold. -/
def GrayChargedExactResolutionInvariantV2 {n b : Nat} (q e a : Nat)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayTailStateV2 n b) : Prop :=
  forall i c, c.val < 2 ^ (e - a) ->
    (GrayTailHasSon st.slots i c ∧
      GrayTailFreshCheckpoint e A sm (frozenV1OfV2 st) i c) ∨
      ((dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailFrozenSonBase (frozenV1OfV2 st) i c) ∧
        GrayTailThresholdExit e A sm (frozenV1OfV2 st) i c ∧
        ¬ GrayTailHasSon st.slots i c) ∨
      (GrayTailPersistentReserveExit e A sm (frozenV1OfV2 st) i c ∧
        grayTailFrozenSonBase (frozenV1OfV2 st) i c <=
          dyadicScale e - dyadicScale e /
            (6 * halfAmplification q) ∧
        ¬ GrayTailHasSon st.slots i c)

/-- Capacity extended one block past the round bound. -/
theorem grayAdvBlock_capacity_succ (q L : Nat) :
    grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q + 1) <=
      grayTailBaseBranch q L := by
  have hRle : grayChargedAdvantageRoundCount q + 1 <= grayTailRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq, grayTailRoundCount]
    have h1 : 1 <= (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hcrude := grayAdvBlockOffset_le_crude q L
    (grayChargedAdvantageRoundCount q + 1)
  have h1 : grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q + 1) <=
      grayTailRoundCount q * 2 ^ ((grayTailRoundCount q - 1) * L) :=
    le_trans hcrude (Nat.mul_le_mul_right _ hRle)
  refine le_trans h1 ?_
  rw [grayTailBaseBranch]
  refine le_trans ?_ (le_max_right _ _)
  rw [grayTailRoundCount]
  set c := 256 * (q + 1) ^ 2 with hc
  have hcfac : c = 256 * (q + 1) * (q + 1) := by rw [hc]; ring
  have hqpow : (q + 1) <= 2 ^ (256 * (q + 1)) := by
    have h1 : q + 1 <= 2 ^ (q + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hexp : (c - 1) * L <= c * L := Nat.mul_le_mul_right L (Nat.sub_le _ _)
  calc c * 2 ^ ((c - 1) * L)
      = 256 * (q + 1) * ((q + 1) * 2 ^ ((c - 1) * L)) := by rw [hcfac]; ring
    _ <= 256 * (q + 1) * (2 ^ (256 * (q + 1)) * 2 ^ (c * L)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul hqpow
        exact Nat.pow_le_pow_right (by norm_num) hexp
    _ = 256 * (q + 1) * 2 ^ (c * L + 256 * (q + 1)) := by
        rw [← pow_add]; ring_nf
    _ = 256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
        rw [hc]

/-- Fit for every round index up to and including the round bound. -/
lemma grayAdvBlock_fit_of_le_advCount {q L a e round : Nat}
    (h : round <= grayChargedAdvantageRoundCount q) :
    grayAdvBlockOffset q L round + grayAdvBlockMult q L round <=
      grayTailBranch q L a e := by
  have hstep : grayAdvBlockOffset q L round + grayAdvBlockMult q L round =
      grayAdvBlockOffset q L (round + 1) :=
    (grayAdvBlockOffset_succ q L round).symm
  have hmono : grayAdvBlockOffset q L (round + 1) <=
      grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q + 1) :=
    grayAdvBlockOffset_mono (by omega)
  have hcap := grayAdvBlock_capacity_succ q L
  have hbase : grayTailBaseBranch q L <= grayTailBranch q L a e :=
    le_max_right _ _
  omega

/-- Grandson blocks are nonempty for every round up to the round bound. -/
lemma grayAdvBlockGrandsons_ne_nil_of_le {q L a e round : Nat}
    (h : round <= grayChargedAdvantageRoundCount q) :
    grayAdvBlockGrandsons (grayTailBranch q L a e) q L round ≠ [] := by
  have hlen := grayAdvBlockGrandsons_length
    (b := grayTailBranch q L a e) (q := q) (L := L) (r := round)
    (grayAdvBlock_fit_of_le_advCount (L := L) (a := a) (e := e) h)
  have hpos := grayAdvBlockMult_pos q L round
  intro hnil
  rw [hnil] at hlen
  simp at hlen
  omega

/-- Nonnegativity of the displayed requests of the current move of a state whose charged block
goal is met. -/
private lemma grayCharged_nonneg_req {n b q L e : Nat} {sigma : FamilyStrategyScheme}
    {st : GrayTailStateV2 n b} {sm_t : FamilyServerMove}
    (hgoal : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length st.unavailable
      (grayBlockCurrentMoveV2 q L e sigma st)
      (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length) st.slots sm_t) = true) :
    forall z, z ∈ grayTailSlotEntries st.slots (grayBlockCurrentMoveV2 q L e sigma st) ->
      0 <= getReq z.2 [] := by
  have hcharged : familyChargedGrayGoalAtB 4 (halfAmplification q)
      (dyadicScale (grayTailRoundEps q L e st.frozen.length))
      ((3 / 4 : Rat) *
        dyadicScale (grayTailRoundEps q L e st.frozen.length))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      st.slots.length st.unavailable
      (grayBlockCurrentMoveV2 q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots
        sm_t) = true := by
    simpa [grayChargedBlockGoalAtB] using hgoal
  obtain ⟨G, _hGmem, hG⟩ :=
    familyChargedGrayGoalAtB.exists_charge hcharged
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hj := (familyGrayChargeAtB.root hG j.isLt).1
  unfold getFamilyReq at hj
  have halpha : 0 <= dyadicScale
      (grayTailRoundEps q L e st.frozen.length) / 2 :=
    (div_pos (dyadicScale_pos _) (by norm_num)).le
  simpa using le_trans halpha hj

/-- The candidate slot list and the narrow tail successor list agree on whether the source
fibre `(i, c)` is occupied after the round `r` over `frozen`.  This is the wide/narrow
occupancy bridge through which the V2 step reuses the V1 argument. -/
private def GrayChargedNarrowBridge {n b : Nat} (q a e r : Nat) (A : Allocation)
    (frozen : GrayTailFrozen n b) (mv : FamilyServerMove)
    (candidates : List (GrayTailSlot n b)) (i : Fin n) (c : Fin b) : Prop :=
  GrayTailHasSon candidates i c ↔
    GrayTailHasSon (grayTailNextSlots e (grayChargedSourceCount a e) r
      (grayTailExitThreshold q e) A frozen mv) i c

/-- The round `p` is stamped at server time `t` and strictly follows every round of the
frozen ledger `frozen`. -/
private def GrayFrozenAcceptsRound {n b : Nat} (frozen : GrayTailFrozen n b)
    (p : GrayTailRound n b) (t : Nat) : Prop :=
  p.serverTime = t ∧ forall p_old, p_old ∈ frozen -> p_old.serverTime < t

/-- Threshold exit in `st` persists after an accepted round `p` that has no son for `(i, c)`. -/
private lemma grayCharged_step_of_threshold_exit {n b q e : Nat} (L : Nat) {A : Allocation}
    {sm : Nat -> FamilyServerMove} {used r t : Nat}
    (frozenV1 : GrayTailFrozen n b) (p : GrayTailRound n b) (i : Fin n) (c : Fin b)
    (hnonneg : 0 <= grayTailSonBase (grayTailSlotEntries p.slots p.move) i c)
    (hclosed : GrayTailChildThresholdClosed q e A sm frozenV1 p.slots i c)
    (hrb : r + 1 < b)
    (hbridge : GrayTailHasSon (grayBlockNextSlots q L e used (r + 1)
        (grayTailExitThreshold q e) A (frozenV1 ++ [p]) (sm t)) i c ↔
      GrayTailHasSon (grayTailNextSlots e used (r + 1)
        (grayTailExitThreshold q e) A (frozenV1 ++ [p]) (sm t)) i c) :
    GrayTailChildThresholdClosed q e A sm (frozenV1 ++ [p])
      (grayBlockNextSlots q L e used (r + 1) (grayTailExitThreshold q e) A
        (frozenV1 ++ [p]) (sm t)) i c := by
  obtain ⟨hthreshold, htexit, hinactive⟩ := hclosed
  have hpnone : ¬ GrayTailRoundHasSon p i c := hinactive
  have hthreshold' : grayTailExitThreshold q e <
      grayTailFrozenSonBase (frozenV1 ++ [p]) i c := by
    rw [grayTailFrozenSonBase_append_global]
    linarith
  refine ⟨hthreshold', htexit.append hpnone, ?_⟩
  intro hn
  have hnarrow := hbridge.1 hn
  have hbelow := ((grayTailHasSon_next_iff hrb i c).1 hnarrow).2.1
  exact hbelow hthreshold'

/-- Persistent reserve exit in `st` is maintained or transitions to a fresh checkpoint
upon adding accepted round `p`. -/
private lemma grayCharged_step_of_reserve_exit {n b q e a r t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (frozenV1 : GrayTailFrozen n b) (p : GrayTailRound n b) (i : Fin n) (c : Fin b)
    (candidates : List (GrayTailSlot n b))
    (haccept : GrayFrozenAcceptsRound frozenV1 p t)
    (hclosed : GrayTailChildReserveClosed q e A sm frozenV1 p.slots i c)
    (hrb : r + 1 < b) (hused' : c.val < grayChargedSourceCount a e)
    (hbridge : GrayChargedNarrowBridge q a e (r + 1) A (frozenV1 ++ [p]) (sm t)
      candidates i c) :
    GrayTailChildOpen e A sm (frozenV1 ++ [p]) candidates i c ∨
      GrayTailChildReserveClosed q e A sm (frozenV1 ++ [p]) candidates i c := by
  obtain ⟨hpserver, hbefore⟩ := haccept
  obtain ⟨hexit, hbasecap, hinactive⟩ := hclosed
  have hpnone : ¬ GrayTailRoundHasSon p i c := hinactive
  have hbasecap' : grayTailFrozenSonBase (frozenV1 ++ [p]) i c <=
      grayTailExitThreshold q e := by
    rw [grayTailFrozenSonBase_append_global,
      grayTailSonBase_eq_zero_of_not_hasSon i c hpnone, add_zero]
    exact hbasecap
  by_cases hnext : GrayTailHasSon candidates i c
  · have hnarrow := hbridge.1 hnext
    have hnone := ((grayTailHasSon_next_iff hrb i c).1 hnarrow).2.2
    left
    refine ⟨hnext, Or.inr ?_⟩
    refine ⟨p, by simp, ?_, ?_⟩
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · rw [hpserver]
        exact (hbefore old hold).le
      · simp only [List.mem_singleton] at hold
        subst old
        exact le_rfl
    · simpa [hpserver] using hnone
  · right
    have hnotnarrow : ¬ GrayTailHasSon
        (grayTailNextSlots e (grayChargedSourceCount a e) (r + 1)
          (grayTailExitThreshold q e) A (frozenV1 ++ [p]) (sm t)) i c :=
      fun hn => hnext (hbridge.2 hn)
    have hremoved := grayTail_missing_after_freeze hrb i c hused' hnotnarrow
    have hreserve := hremoved.resolve_left (not_lt_of_ge hbasecap')
    obtain ⟨R, hR⟩ := (getTailFamilyReserve_isSome_iff e _ A n i.val (sm t) [c.val]).mp hreserve
    obtain ⟨pre, last, post, reserveTime, oldR, hsplit, hlast,
      _holdR, _holdmax, hfreshx, hpost⟩ := hexit
    refine ⟨?_, hbasecap', hnext⟩
    refine ⟨pre, last, post ++ [p], t, R, ?_, hlast, hR, ?_, hfreshx, ?_⟩
    · have hsplit' : frozenV1 = pre ++ last :: post := hsplit
      rw [hsplit', List.append_assoc]
      simp
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact (hbefore old hold).le
      · simp only [List.mem_singleton] at hold
        subst old
        rw [hpserver]
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · exact hpost old hold
      · simp only [List.mem_singleton] at hold
        subst old
        exact hpnone

/-- Active fibre in `st` either stays active or exits (threshold or reserve exit)
after accepted round `p`. -/
private lemma grayCharged_step_of_active {n b q e a r t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (frozenV1 : GrayTailFrozen n b) (p : GrayTailRound n b) (i : Fin n) (c : Fin b)
    (candidates : List (GrayTailSlot n b))
    (haccept : GrayFrozenAcceptsRound frozenV1 p t)
    (hopen : GrayTailChildOpen e A sm frozenV1 p.slots i c)
    (hrb : r + 1 < b) (hused' : c.val < grayChargedSourceCount a e)
    (hbridge : GrayChargedNarrowBridge q a e (r + 1) A (frozenV1 ++ [p]) (sm t)
      candidates i c) :
    GrayTailChildOpen e A sm (frozenV1 ++ [p]) candidates i c ∨
      GrayTailChildThresholdClosed q e A sm (frozenV1 ++ [p]) candidates i c ∨
      GrayTailChildReserveClosed q e A sm (frozenV1 ++ [p]) candidates i c := by
  obtain ⟨hpserver, hbefore⟩ := haccept
  obtain ⟨hcurrent, hfresh⟩ := hopen
  by_cases hnext : GrayTailHasSon candidates i c
  · have hnarrow := hbridge.1 hnext
    have hnone := ((grayTailHasSon_next_iff hrb i c).1 hnarrow).2.2
    left
    refine ⟨hnext, Or.inr ?_⟩
    refine ⟨p, by simp, ?_, ?_⟩
    · intro old hold
      rcases List.mem_append.mp hold with hold | hold
      · rw [hpserver]
        exact (hbefore old hold).le
      · simp only [List.mem_singleton] at hold
        subst old
        exact le_rfl
    · simpa [hpserver] using hnone
  · right
    have hnotnarrow : ¬ GrayTailHasSon
        (grayTailNextSlots e (grayChargedSourceCount a e) (r + 1)
          (grayTailExitThreshold q e) A (frozenV1 ++ [p]) (sm t)) i c :=
      fun hn => hnext (hbridge.2 hn)
    have hremoved := grayTail_missing_after_freeze hrb i c hused' hnotnarrow
    by_cases hbase : grayTailExitThreshold q e <
        grayTailFrozenSonBase (frozenV1 ++ [p]) i c
    · left
      refine ⟨hbase, ?_, hnext⟩
      refine ⟨frozenV1, p, [], by simp, hcurrent, ?_, by simp⟩
      rcases hfresh with hempty | ⟨last, hlast, hmax, hnone⟩
      · exact Or.inl hempty
      · exact Or.inr ⟨last.serverTime, hmax,
          by rw [hpserver]; exact (hbefore last hlast).le, hnone⟩
    · right
      have hreserve := hremoved.resolve_left hbase
      obtain ⟨R, hR⟩ := (getTailFamilyReserve_isSome_iff e _ A n i.val (sm t) [c.val]).mp hreserve
      refine ⟨?_, le_of_not_gt hbase, hnext⟩
      refine ⟨frozenV1, p, [], t, R, by simp, hcurrent, hR, ?_, ?_, by simp⟩
      · intro old hold
        rcases List.mem_append.mp hold with hold | hold
        · simpa [hpserver] using (hbefore old hold).le
        · simp only [List.mem_singleton] at hold
          subst old
          rw [hpserver]
      · rcases hfresh with hempty | ⟨last, hlast, hmax, hnone⟩
        · exact Or.inl hempty
        · exact Or.inr ⟨last.serverTime, hmax,
            by rw [hpserver]; exact (hbefore last hlast).le, hnone⟩

/-- **The V2 exact resolution invariant is preserved by the strict block
step** (mirror of the V1 proof through the wide/narrow occupancy bridge). -/
lemma grayChargedExactResolutionInvariantV2_step
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (st : GrayTailStateV2 n (grayTailBranch q L a e)) (htime : st.time = t)
    (hbefore : forall p, p ∈ st.frozen -> p.serverTime < t)
    (hround : st.done = false ->
      st.frozen.length < grayChargedAdvantageRoundCount q)
    (hprev : GrayChargedExactResolutionInvariantV2 q e a A sm st) :
    GrayChargedExactResolutionInvariantV2 q e a A sm
      (grayChargedBlockTailStepV2 q L a e sigma A st (sm t)) := by
  intro i c hused
  by_cases hd : st.done = true
  · simpa [grayChargedBlockTailStepV2, hd, frozenV1OfV2] using hprev i c hused
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedBlockTailStepV2, hd', hs, frozenV1OfV2] using
        hprev i c hused
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      by_cases hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable
          (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm t)) = true
      · -- accept branch: rewrite via the accept equations
        have hRC := hround hd'
        have hfzEq := grayChargedBlockTailStepV2_accept_frozen_eq
          q L a e sigma A st (sm t) hd' hs' hgoal
        have hslEq := grayChargedBlockTailStepV2_accept_slots
          q L a e sigma A st (sm t) hd' hs' hgoal
        have hflen := grayChargedBlockTailStepV2_accept_frozen
          q L a e sigma A st (sm t) hd' hs' hgoal
        set pV2 : GrayTailRoundV2 n (grayTailBranch q L a e) :=
          { serverTime := st.time
            roundIndex := st.frozen.length
            blockAnchor := grayTailRoundEps q L e st.frozen.length
            childEps := grayTailRoundEps q L e st.frozen.length +
              graySpendSpan q
            fineEnd := grayTailRoundDelta q L e st.frozen.length
            slots := st.slots
            move := grayBlockCurrentMoveV2 q L e sigma st
            allocated := grayTailLocalAllocatedList
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t))
            unavailable := st.unavailable } with hpV2
        set p : GrayTailRound n (grayTailBranch q L a e) := pV2.toV1 with hp
        set frozenV1 := st.frozen.map GrayTailRoundV2.toV1 with hfv1
        set frozen' := frozenV1 ++ [p] with hfz
        set threshold := grayTailExitThreshold q e with hth
        have hpserver : p.serverTime = t := by
          rw [hp, hpV2]
          simpa [GrayTailRoundV2.toV1] using htime
        have hprojEq : frozenV1OfV2
            (grayChargedBlockTailStepV2 q L a e sigma A st (sm t)) =
            frozen' := by
          rw [frozenV1OfV2, hfzEq, List.map_append, List.map_cons,
            List.map_nil, hfz, hfv1, hp, hpV2]
        have hmapEq : (grayChargedBlockTailStepV2 q L a e sigma A st
            (sm t)).frozen.map GrayTailRoundV2.toV1 = frozen' := hprojEq
        have hslEq' : (grayChargedBlockTailStepV2 q L a e sigma A st
            (sm t)).slots =
            grayBlockNextSlots q L e (grayChargedSourceCount a e)
              (st.frozen.length + 1) threshold A frozen' (sm t) := by
          rw [hslEq, hmapEq, hflen, hth, grayTailExitThreshold]
        set candidates := grayBlockNextSlots q L e
          (grayChargedSourceCount a e) (st.frozen.length + 1) threshold A
          frozen' (sm t) with hcand
        rw [hprojEq, hslEq']
        have hrb : st.frozen.length + 1 < grayTailBranch q L a e := by
          have hlt := grayChargedAdvantageRoundCount_lt_branch q L a e
          omega
        have hGne : grayAdvBlockGrandsons (grayTailBranch q L a e) q L
            (st.frozen.length + 1) ≠ [] :=
          grayAdvBlockGrandsons_ne_nil_of_le (by omega)
        have hbridge := grayBlockHasSon_iff (n := n)
          (q := q) (L := L) (e := e)
          (used := grayChargedSourceCount a e)
          (round := st.frozen.length + 1) (threshold := threshold)
          (A := A) (frozen := frozen') (sm := sm t) hrb hGne i c
        have hused' : c.val < grayChargedSourceCount a e := by
          simpa [grayChargedSourceCount] using hused
        have hbeforeV1 : forall p_old, p_old ∈ frozenV1 -> p_old.serverTime < t := by
          intro p_old hold
          rw [hfv1, List.mem_map] at hold
          obtain ⟨pV2', hold', rfl⟩ := hold
          simpa [GrayTailRoundV2.toV1] using hbefore pV2' hold'
        have hreq : forall z, z ∈ grayTailSlotEntries p.slots p.move ->
            0 <= getReq z.2 [] := by
          simpa [hp, hpV2, GrayTailRoundV2.toV1] using grayCharged_nonneg_req hgoal
        have hpnonneg : 0 <= grayTailSonBase (grayTailSlotEntries p.slots p.move) i c :=
          grayTailSonBase_nonneg_global hreq
        have haccept : GrayFrozenAcceptsRound frozenV1 p t := ⟨hpserver, hbeforeV1⟩
        rcases hprev i c hused with ⟨hcurrent, hfresh⟩ | hresolved
        · exact grayCharged_step_of_active (r := st.frozen.length) frozenV1 p i c candidates
            haccept ⟨by simpa [hp, hpV2, GrayTailRoundV2.toV1] using hcurrent,
              by simpa [hfv1, frozenV1OfV2] using hfresh⟩ hrb hused' hbridge
        · rcases hresolved with ⟨hthreshold, htexit, hinactive⟩ | ⟨hexit, hbasecap, hinactive⟩
          · right; left
            have hpnone : ¬ GrayTailRoundHasSon p i c := by
              simpa [hp, hpV2, GrayTailRoundV2.toV1, GrayTailRoundHasSon] using hinactive
            exact grayCharged_step_of_threshold_exit L (r := st.frozen.length)
              frozenV1 p i c hpnonneg
              ⟨by exact hthreshold,
                by simpa [hfv1, frozenV1OfV2] using htexit, hpnone⟩ hrb hbridge
          · have hpnone : ¬ GrayTailRoundHasSon p i c := by
              simpa [hp, hpV2, GrayTailRoundV2.toV1, GrayTailRoundHasSon] using hinactive
            rcases grayCharged_step_of_reserve_exit (r := st.frozen.length) frozenV1
              p i c candidates haccept
              ⟨by simpa [hfv1, frozenV1OfV2] using hexit,
                by exact hbasecap, hpnone⟩ hrb hused'
              hbridge with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inr h2)
      · simpa [grayChargedBlockTailStepV2, hd', hs', hgoal,
          frozenV1OfV2] using hprev i c hused

/-- Every used fibre is occupied in the initial wide block. -/
lemma grayAdvBlockSlots_hasSon {n b used q L r : Nat}
    (i : Fin n) (c : Fin b) (hused : c.val < used)
    (hG : grayAdvBlockGrandsons b q L r ≠ []) :
    GrayTailHasSon (grayAdvBlockSlots n b used q L r) i c := by
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hG
  refine ⟨(i, c, g), ?_, rfl, rfl⟩
  rw [grayAdvBlockSlots, List.mem_flatMap]
  refine ⟨i, List.mem_finRange _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_filter.mpr ⟨List.mem_finRange _, by
    simpa using hused⟩, ?_⟩
  rw [List.mem_map]
  exact ⟨g, hg, rfl⟩

/-- The V2 exact resolution invariant holds along the strict advantage
trajectory. -/
theorem grayChargedExactResolutionInvariantV2_stateAt
    {n q L a e : Nat} (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedExactResolutionInvariantV2 q e a A sm
      (grayChargedBlockTailStateAtV2
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      intro i c hused
      left
      constructor
      · change GrayTailHasSon
          (grayChargedBlockTailInitialStateV2 n (grayTailBranch q L a e)
            a e q L A).slots i c
        apply grayAdvBlockSlots_hasSon i c
          (by simpa [grayChargedSourceCount] using hused)
        exact grayAdvBlockGrandsons_ne_nil_of_le (by omega)
      · exact Or.inl rfl
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      apply grayChargedExactResolutionInvariantV2_step
        (t := t) (sm := sm) _
      · exact (grayChargedBlockTailCertifiedV2_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).time_eq
      · intro p hp
        exact ((grayChargedBlockTailCertifiedV2_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).round_valid p hp).2.2.2.2.1
      · intro hdoneFalse
        exact (grayChargedBlockTailCertifiedV2_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).frozen_bound.2 hdoneFalse
      · exact ih

/-- **The V2 terminal resolution** (detailed form): once a used fibre is
inactive at a terminal state, it threshold-exited with its last-call
certificate, or persistent-reserve-exited with a small base. -/
theorem grayChargedBlockTail_terminal_detailed_resolution
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < 2 ^ (e - a) ->
      ¬ GrayTailHasSon
        (grayChargedBlockTailStateAtV2
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots i c ->
      ((dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailFrozenSonBase
            (frozenV1OfV2 (grayChargedBlockTailStateAtV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) i c) ∧
        GrayTailThresholdExit e A sm
          (frozenV1OfV2 (grayChargedBlockTailStateAtV2
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t)) i c) ∨
      (GrayTailPersistentReserveExit e A sm
          (frozenV1OfV2 (grayChargedBlockTailStateAtV2
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t)) i c ∧
        grayTailFrozenSonBase
            (frozenV1OfV2 (grayChargedBlockTailStateAtV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) i c <=
          dyadicScale e - dyadicScale e /
            (6 * halfAmplification q)) := by
  intro i c hused hinactive
  have hinv := grayChargedExactResolutionInvariantV2_stateAt
    (n := n) (L := L) sigma A sm t i c hused
  rcases hinv with hactive | hresolved
  · exact (hinactive hactive.1).elim
  · rcases hresolved with ⟨hthreshold, htexit, _⟩ |
      ⟨hexit, hbasecap, _⟩
    · exact Or.inl ⟨hthreshold, htexit⟩
    · exact Or.inr ⟨hexit, hbasecap⟩

end Kolmogorov
