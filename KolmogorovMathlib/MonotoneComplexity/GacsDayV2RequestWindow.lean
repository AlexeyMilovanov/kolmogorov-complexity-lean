import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Ledger
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow

/-!
# The V2 request window (Stage C3, pinned gap)

The per-pass increment bounds of the V2 spend blocks: at the pinned gap each
pass hands every deficient root a block of `graySpendMult L pass` children
whose displayed requests aggregate into the Day window `[α/16, α/8]` — the
C1 multiplicities recover exactly the committed per-pass increment.
-/

namespace Kolmogorov

/-- Root-fibre length of one V2 spend slot list. -/
lemma grayBlockSpendSlotsV2_filter_root_length {n b : Nat}
    (source L pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) (i : Fin n) :
    ((grayBlockSpendSlotsV2 source L pass threshold eps alpha frozen).filter
        fun s => decide (s.1 = i)).length =
      if i ∈ grayChargedDeficientRoots source threshold eps alpha frozen then
        (grayBlockSpendPairs b source L pass).length
      else 0 := by
  unfold grayBlockSpendSlotsV2
  exact grayCharged_filter_flatMap_root_length _ _
    (grayChargedDeficientRoots_nodup source threshold eps alpha frozen) i

/-- The pinned pass block has its full multiplicity. -/
lemma grayBlockSpendPairs_length_pinned {q L a e pass : Nat}
    (hpin : e = a + 8 * L + 3) (hpass : pass < 8) :
    (grayBlockSpendPairs (grayTailBranch q L a e)
        (grayChargedSourceCount a e) L pass).length =
      graySpendMult L pass := by
  apply grayBlockSpendPairs_length hpass
  have hcap := grayBlockSpend_capacity (q := q) (L := L) (a := a) (e := e)
    hpin
  have hb : 1 <= grayTailBranch q L a e := by
    refine le_trans ?_ (le_max_left (2 * 2 ^ (e - a)) _)
    have : (1 : Nat) <= 2 ^ (e - a) := Nat.one_le_two_pow
    omega
  calc grayBlockSpendOffset L 8
      <= grayTailBranch q L a e - grayChargedSourceCount a e := hcap
    _ = (grayTailBranch q L a e - grayChargedSourceCount a e) * 1 := by ring
    _ <= (grayTailBranch q L a e - grayChargedSourceCount a e) *
          grayTailBranch q L a e :=
        Nat.mul_le_mul_left _ hb

/-- The pinned block-mass identity in `α`-form: the pass block aggregates to
`dyadicScale a / 8` (one Day increment). -/
lemma graySpendBlockV2_alpha_mass {_q a L e pass : Nat}
    (hpin : e = a + 8 * L + 3) (hpass : pass < 8) :
    (graySpendMult L pass : Rat) *
        dyadicScale (grayChargedSpendEps a L e pass) =
      dyadicScale a / 8 := by
  subst hpin
  exact graySpendBlock_pinned_mass a L pass hpass

/-- **The V2 per-pass increment bounds** (pinned gap): an accepted spend
block pass hands each deficient root an aggregate displayed increment in the
Day window `[α/16, α/8]`. -/
lemma grayBlockRootIncrementV2_spend_bounds
    {q L a e n pass : Nat} {A : Allocation}
    (hpin : e = a + 8 * L + 3) (hpass : pass < 8)
    (frozen : GrayTailFrozen n (grayTailBranch q L a e))
    (move : FamilyClientMove) (server : FamilyServerMove)
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass
      (grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
        (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
        frozen).length A move server = true)
    (i : Fin n)
    (hi : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen) :
    dyadicScale a / 16 <=
        grayChargedRootIncrement
          (grayTailSlotEntries
            (grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
              (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
              frozen) move) i ∧
      grayChargedRootIncrement
          (grayTailSlotEntries
            (grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
              (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
              frozen) move) i <=
        dyadicScale a / 8 := by
  set slots := grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
    (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen
    with hslotsDef
  set rootslots := Finset.univ.filter
    (fun j : Fin slots.length => (slots.get j).1 = i) with hrootsDef
  have hcard : rootslots.card = graySpendMult L pass := by
    calc
      rootslots.card =
          (slots.filter fun s => decide (s.1 = i)).length := by
            simpa [rootslots, List.get_eq_getElem] using
              grayCharged_filter_index_card slots i
      _ = graySpendMult L pass := by
        rw [hslotsDef, grayBlockSpendSlotsV2_filter_root_length, if_pos hi,
          grayBlockSpendPairs_length_pinned hpin hpass]
  have hsum :
      grayChargedRootIncrement (grayTailSlotEntries slots move) i =
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
    rw [grayChargedRootIncrement_slotEntries_eq_sum]
    dsimp [rootslots]
    rw [Finset.sum_filter]
  have hlower :
      (∑ _j ∈ rootslots,
          dyadicScale (grayChargedSpendEps a L e pass) / 2) <=
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
    apply Finset.sum_le_sum
    intro j hj
    exact (grayChargedBlockSpendGoalAtB_root_bounds hgoal j).1
  have hupper :
      (∑ j ∈ rootslots, getFamilyReq move j.val []) <=
        ∑ _j ∈ rootslots, dyadicScale (grayChargedSpendEps a L e pass) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (grayChargedBlockSpendGoalAtB_root_bounds hgoal j).2
  have hmass := @graySpendBlockV2_alpha_mass q a L e pass hpin hpass
  have hquarter :
      (graySpendMult L pass : Rat) *
          (dyadicScale (grayChargedSpendEps a L e pass) / 2) =
        dyadicScale a / 16 := by
    calc
      (graySpendMult L pass : Rat) *
            (dyadicScale (grayChargedSpendEps a L e pass) / 2) =
          ((graySpendMult L pass : Rat) *
            dyadicScale (grayChargedSpendEps a L e pass)) / 2 := by ring
      _ = (dyadicScale a / 8) / 2 := by rw [hmass]
      _ = dyadicScale a / 16 := by ring
  constructor
  · calc
      dyadicScale a / 16 =
          (rootslots.card : Rat) *
            (dyadicScale (grayChargedSpendEps a L e pass) / 2) := by
              rw [hcard]
              exact hquarter.symm
      _ = ∑ _j ∈ rootslots,
            dyadicScale (grayChargedSpendEps a L e pass) / 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ∑ j ∈ rootslots, getFamilyReq move j.val [] := hlower
      _ = grayChargedRootIncrement (grayTailSlotEntries slots move) i :=
        hsum.symm
  · rw [hsum]
    calc
      (∑ j ∈ rootslots, getFamilyReq move j.val []) <=
          ∑ _j ∈ rootslots,
            dyadicScale (grayChargedSpendEps a L e pass) := hupper
      _ = (rootslots.card : Rat) *
            dyadicScale (grayChargedSpendEps a L e pass) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = (graySpendMult L pass : Rat) *
            dyadicScale (grayChargedSpendEps a L e pass) := by rw [hcard]
      _ = dyadicScale a / 8 := hmass

/-- A non-deficient root receives no V2 spend slots. -/
lemma grayBlockRootIncrementV2_spend_eq_zero
    {q L a e n pass : Nat}
    (frozen : GrayTailFrozen n (grayTailBranch q L a e))
    (move : FamilyClientMove) (i : Fin n)
    (hi : i ∉ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen) :
    grayChargedRootIncrement
        (grayTailSlotEntries
          (grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
            (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
            frozen) move) i = 0 := by
  set slots := grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
    (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen
    with hslotsDef
  set rootslots := Finset.univ.filter
    (fun j : Fin slots.length => (slots.get j).1 = i) with hrootsDef
  have hcard : rootslots.card = 0 := by
    calc
      rootslots.card =
          (slots.filter fun s => decide (s.1 = i)).length := by
            simpa [rootslots, List.get_eq_getElem] using
              grayCharged_filter_index_card slots i
      _ = 0 := by
        rw [hslotsDef, grayBlockSpendSlotsV2_filter_root_length, if_neg hi]
  have hempty : rootslots = ∅ := Finset.card_eq_zero.mp hcard
  rw [grayChargedRootIncrement_slotEntries_eq_sum]
  calc
    (∑ j : Fin slots.length,
        if (slots.get j).1 = i then getFamilyReq move j.val [] else 0) =
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
          dsimp [rootslots]
          rw [Finset.sum_filter]
    _ = 0 := by simp [hempty]

/-- Root request bounds of the strict V2 advantage tail (projected). -/
lemma grayChargedBlockTailV2_frozen_root_bounds_stateAt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (i : Fin n) :
    0 <= grayChargedFrozenRootRequest q a e
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t)) i ∧
      grayChargedFrozenRootRequest q a e
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t)) i <= dyadicScale a := by
  set frozen := frozenV1OfV2 (grayChargedBlockTailStateAtV2
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t) with hfz
  set entries := grayTailFrozenEntries frozen with hentriesDef
  have hentryNonneg : ∀ z ∈ entries, 0 <= getReq z.2 [] := by
    intro z hz
    rw [hentriesDef, hfz, grayTailFrozenEntries, List.mem_flatMap] at hz
    obtain ⟨pV1, hpV1, hzp⟩ := hz
    rw [frozenV1OfV2, List.mem_map] at hpV1
    obtain ⟨p, hp, rfl⟩ := hpV1
    have hgoal := ((grayChargedBlockTailCertifiedV2_stateAt (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm t).round_valid p hp).2.2.2.2.2.2.1
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hzp
    have hj := (grayChargedBlockGoalAtB_root_bounds hgoal
      (⟨j.val, by simp [GrayTailRoundV2.toV1]⟩ : Fin _)).1
    have hpos : (0 : Rat) <=
        dyadicScale (grayTailRoundEps q L e p.roundIndex) / 2 :=
      div_nonneg (dyadicScale_pos _).le (by norm_num)
    have hnn : (0 : Rat) <= getFamilyReq p.move j.val [] :=
      le_trans hpos hj
    simpa [getFamilyReq, GrayTailRoundV2.toV1] using hnn
  have hson : ∀ c : Fin (grayTailBranch q L a e),
      0 <= grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c ∧
        grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c <=
            if c.val < grayChargedSourceCount a e then dyadicScale e
            else 0 := by
    intro c
    by_cases hc : c.val < grayChargedSourceCount a e
    · unfold grayChargedSonRequest grayTailSonRequest
      simp only [if_pos hc]
      by_cases hlarge : grayChargedThreshold q e <
          grayTailSonBase entries i c
      · rw [if_pos hlarge]
        exact ⟨(dyadicScale_pos e).le, le_rfl⟩
      · rw [if_neg hlarge]
        constructor
        · exact grayTailSonBase_nonneg_global hentryNonneg
        · have hbase := grayChargedBlockV2_all_frozen_base_le_stateAt
            q L a e sigma A sm t i c
          simpa [frozen, entries, hentriesDef, hfz,
            grayTailFrozenSonBase] using hbase
    · have hzero : grayTailSonBase entries i c = 0 := by
        apply grayTailSonBase_eq_zero_of_no_match
        intro z hz
        right
        intro hzc
        have hzlt := grayChargedBlockV2_frozenEntries_used
          (q := q) (L := L) (a := a) (e := e)
          (sigma := sigma) (A := A) (sm := sm) (t := t)
          (by simpa [entries, hentriesDef, hfz] using hz)
        have heq : z.1.2.1.val = c.val := congrArg Fin.val hzc
        rw [heq] at hzlt
        exact (Nat.not_lt_of_ge (by
          simpa [grayChargedSourceCount] using Nat.le_of_not_gt hc)) hzlt
      unfold grayChargedSonRequest
      simp only [if_neg hc, hzero]
      norm_num
  unfold grayChargedFrozenRootRequest grayChargedRootRequest
  constructor
  · apply Finset.sum_nonneg
    intro c hc
    exact (hson c).1
  · calc
      (∑ c : Fin (grayTailBranch q L a e),
          grayChargedSonRequest
            (grayChargedSourceCount a e) (grayChargedThreshold q e)
            (dyadicScale e) entries i c) <=
          ∑ c : Fin (grayTailBranch q L a e),
            if c.val < grayChargedSourceCount a e then dyadicScale e
            else 0 := by
              apply Finset.sum_le_sum
              intro c hc
              exact (hson c).2
      _ = ∑ c ∈ Finset.univ.filter
            (fun c : Fin (grayTailBranch q L a e) =>
              c.val < grayChargedSourceCount a e), dyadicScale e := by
              rw [Finset.sum_filter]
      _ = ((Finset.univ.filter
            (fun c : Fin (grayTailBranch q L a e) =>
              c.val < grayChargedSourceCount a e)).card : Rat) *
            dyadicScale e := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (grayChargedSourceCount a e : Rat) * dyadicScale e := by
        apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
        exact_mod_cast grayTail_source_fin_card_le
          (grayTailBranch q L a e) (grayChargedSourceCount a e)
      _ = dyadicScale a := grayChargedSource_mass hae

/-- Empty V2 pass slots force the done window (pinned gap). -/
lemma grayChargedDoneWindowV2_of_slots_nil {q L a e n pass : Nat}
    {frozen : GrayTailFrozen n (grayTailBranch q L a e)}
    (hpin : e = a + 8 * L + 3) (hpass : pass < 8)
    (hwindow : GrayChargedSpendWindow q a e pass frozen)
    (hslots : grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
      (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
      frozen = []) :
    GrayChargedDoneWindow q a e frozen := by
  intro i
  have hi := hwindow i
  constructor
  · by_contra hhalf
    have hlt : grayChargedFrozenRootRequest q a e frozen i <
        dyadicScale a / 2 := lt_of_not_ge hhalf
    have hmem : i ∈ grayChargedDeficientRoots
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen :=
      (mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).2 hlt
    have hlen := grayBlockSpendSlotsV2_filter_root_length
      (grayChargedSourceCount a e) L pass
      (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a) frozen i
    rw [hslots, if_pos hmem,
      grayBlockSpendPairs_length_pinned hpin hpass] at hlen
    have hmultPos : 0 < graySpendMult L pass := by
      unfold graySpendMult
      positivity
    simp at hlen
    omega
  · exact hi.2.1

/-- One accepted V2 spend pass advances the window (pinned gap). -/
lemma grayChargedSpendWindowV2_append_round
    {q L a e n pass : Nat} {U : Allocation}
    {frozen : GrayTailFrozen n (grayTailBranch q L a e)}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    {server : FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hpass : pass < 8)
    (hwindow : GrayChargedSpendWindow q a e pass frozen)
    (hslots : p.slots = grayBlockSpendSlotsV2 (grayChargedSourceCount a e)
      L pass (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
      frozen)
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass
      p.slots.length U p.move server = true)
    (hspare : ∀ s ∈ p.slots, grayChargedSourceCount a e <= s.2.1.val) :
    GrayChargedSpendWindow q a e (pass + 1) (frozen ++ [p]) := by
  intro i
  have hreq := grayChargedRootRequest_append_spend_round
    (grayChargedThreshold q e) (dyadicScale e) frozen p hspare i
  change 0 <= grayChargedFrozenRootRequest q a e (frozen ++ [p]) i ∧
    grayChargedFrozenRootRequest q a e (frozen ++ [p]) i <= dyadicScale a ∧
    (grayChargedFrozenRootRequest q a e (frozen ++ [p]) i <
      dyadicScale a / 2 ->
      ((pass + 1 : Nat) : Rat) * (dyadicScale a / 16) <=
        grayChargedFrozenRootRequest q a e (frozen ++ [p]) i)
  symm at hreq
  change grayChargedFrozenRootRequest q a e frozen i +
      grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i =
    grayChargedFrozenRootRequest q a e (frozen ++ [p]) i at hreq
  have hold := hwindow i
  by_cases hdef : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen
  · have hlt : grayChargedFrozenRootRequest q a e frozen i <
        dyadicScale a / 2 :=
      (mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).1 hdef
    have hinc := grayBlockRootIncrementV2_spend_bounds
      (q := q) (L := L) (a := a) (e := e) (pass := pass)
      (A := U) hpin hpass frozen p.move server
      (by simpa [hslots] using hgoal) i hdef
    have hinc' : dyadicScale a / 16 <=
          grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i ∧
        grayChargedRootIncrement (grayTailSlotEntries p.slots p.move) i <=
          dyadicScale a / 8 := by
      simpa [hslots] using hinc
    constructor
    · rw [← hreq]
      linarith [hinc'.1]
    constructor
    · rw [← hreq]
      linarith [hinc'.2]
    · intro _hnew
      have holdLower := hold.2.2 hlt
      rw [← hreq]
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith [hinc'.1]
  · have hinc := grayBlockRootIncrementV2_spend_eq_zero
      (q := q) (L := L) (a := a) (e := e) (pass := pass)
      frozen p.move i hdef
    have hsame : grayChargedFrozenRootRequest q a e (frozen ++ [p]) i =
        grayChargedFrozenRootRequest q a e frozen i := by
      rw [← hreq, hslots, hinc, add_zero]
    rw [hsame]
    refine ⟨hold.1, hold.2.1, ?_⟩
    intro hlt
    exact False.elim (hdef
      ((mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) frozen i).2 hlt))

/-- The phase-indexed root-request window of a V2 charged state, read on the V1 projection of the
frozen ledger: no condition in the advantage phase, `GrayChargedSpendWindow q a e pass` in spend
pass `pass`, and `GrayChargedDoneWindow q a e` in the done phase. -/
def GrayChargedRequestInvariantV2 {n b : Nat}
    (q a e : Nat) (st : GrayChargedStateV2 n b) : Prop :=
  match st.phase with
  | .advantage => True
  | .spend pass => GrayChargedSpendWindow q a e pass
      (st.core.frozen.map GrayTailRoundV2.toV1)
  | .done => GrayChargedDoneWindow q a e
      (st.core.frozen.map GrayTailRoundV2.toV1)

/-- Starting spend phase preserves the request invariant when exiting advantage. -/
private lemma grayChargedStartSpendV2_invariant_of_done
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e) (t : Nat)
    (core : GrayTailStateV2 n (grayTailBranch q L a e))
    (hcoreTail' : core = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)
    (_hdone : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true) :
    GrayChargedRequestInvariantV2 q a e
      (grayChargedStartSpendV2 q L a e A
        (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t)) := by
  have hnextEq : grayChargedBlockTailStepV2 q L a e sigma A core
      (sm t) = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1) := by
    rw [grayChargedBlockTailStateAtV2_succ]
    rw [hcoreTail']
  have hbounds : ∀ i : Fin n,
      0 <= grayChargedFrozenRootRequest q a e
        ((grayChargedBlockTailStepV2 q L a e sigma A core
          (sm t)).frozen.map GrayTailRoundV2.toV1) i ∧
        grayChargedFrozenRootRequest q a e
          ((grayChargedBlockTailStepV2 q L a e sigma A core
            (sm t)).frozen.map GrayTailRoundV2.toV1) i <=
          dyadicScale a := by
    intro i
    have hi := grayChargedBlockTailV2_frozen_root_bounds_stateAt
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) (t := t + 1) hae i
    rw [← hnextEq] at hi
    simpa [frozenV1OfV2] using hi
  have hwindow0 : GrayChargedSpendWindow q a e 0
      ((grayChargedBlockTailStepV2 q L a e sigma A core
        (sm t)).frozen.map GrayTailRoundV2.toV1) :=
    grayChargedSpendWindow_zero_of_bounds hbounds
  by_cases hempty :
      (grayChargedSlotsForPassV2 q L a e 0
        (grayChargedBlockTailStepV2 q L a e sigma A core
          (sm t)).frozen).isEmpty = true
  · have hnil : grayChargedSlotsForPassV2 q L a e 0
        (grayChargedBlockTailStepV2 q L a e sigma A core
          (sm t)).frozen = [] :=
      List.isEmpty_iff.mp hempty
    have hdoneWindow := grayChargedDoneWindowV2_of_slots_nil
      (q := q) (L := L) (a := a) (e := e)
      (pass := 0) hpin (by omega) hwindow0
      (by simpa [grayChargedSlotsForPassV2] using hnil)
    simpa [grayChargedStartSpendV2, _hdone, hempty,
      GrayChargedRequestInvariantV2] using hdoneWindow
  · have hfalse :
        (grayChargedSlotsForPassV2 q L a e 0
          (grayChargedBlockTailStepV2 q L a e sigma A core
            (sm t)).frozen).isEmpty = false := by
      cases h : (grayChargedSlotsForPassV2 q L a e 0
          (grayChargedBlockTailStepV2 q L a e sigma A core
            (sm t)).frozen).isEmpty <;> simp_all
    simpa [grayChargedStartSpendV2, _hdone, hfalse,
      GrayChargedRequestInvariantV2] using hwindow0

/-- Taking a step in the advantage phase preserves the V2 request invariant. -/
private lemma grayChargedRequestInvariantV2_step_advantage
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e) (t : Nat)
    (core : GrayTailStateV2 n (grayTailBranch q L a e))
    (hcoreTail' : core = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t) :
    GrayChargedRequestInvariantV2 q a e
      (grayChargedStepV2 q L a e sigma A
        { phase := .advantage, core := core } (sm t)) := by
  have hphase' : ({ phase := .advantage, core := core } :
      GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage :=
    rfl
  by_cases hdone :
      (grayChargedBlockTailStepV2 q L a e sigma A core
        (sm t)).done = true
  · by_cases hserved : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) =
          true
    · rw [grayChargedStepV2_advantage_exit q L a e sigma A
        { phase := .advantage, core := core } (sm t) hphase' hdone hserved]
      exact grayChargedStartSpendV2_invariant_of_done
        hpin hae t core hcoreTail' hdone
    · have hserved' : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t))
            (sm t) = false := by
        simpa using hserved
      rw [grayChargedStepV2_advantage_wait q L a e sigma A
        { phase := .advantage, core := core } (sm t) hphase' hdone hserved']
      simp [GrayChargedRequestInvariantV2]
  · simp [grayChargedStepV2, hdone, GrayChargedRequestInvariantV2]

/-- Taking a step in the spend phase preserves the V2 request invariant. -/
private lemma grayChargedRequestInvariantV2_step_spend
    {q L a e n pass : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t : Nat}
    (hpin : e = a + 8 * L + 3)
    (core : GrayTailStateV2 n (grayTailBranch q L a e))
    (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass core)
    (hwindow : GrayChargedSpendWindow q a e pass
      (core.frozen.map GrayTailRoundV2.toV1)) :
    GrayChargedRequestInvariantV2 q a e
      (grayChargedStepV2 q L a e sigma A
        { phase := .spend pass, core := core } (sm t)) := by
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
      core.slots.length core.unavailable
      (grayBlockSpendMoveV2 q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
        core.slots (sm t)) = true
  · set pV2 : GrayTailRoundV2 n (grayTailBranch q L a e) :=
      { serverTime := core.time
        roundIndex := core.frozen.length
        blockAnchor := grayChargedSpendEps a L e pass
        childEps := grayChargedSpendEps a L e pass + graySpendSpan q
        fineEnd := grayChargedSpendDelta a L e pass
        slots := core.slots
        move := grayBlockSpendMoveV2 q L a e pass sigma core
        allocated := grayTailLocalAllocatedList
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
            core.slots (sm t))
        unavailable := core.unavailable } with hpV2
    have hpSlots : pV2.toV1.slots =
        grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
          (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
          (core.frozen.map GrayTailRoundV2.toV1) := by
      have := hspend.slots_eq
      simpa [hpV2, GrayTailRoundV2.toV1,
        grayChargedSlotsForPassV2] using this
    have hspare : ∀ s ∈ pV2.toV1.slots,
        grayChargedSourceCount a e <= s.2.1.val := by
      intro s hs
      apply grayBlockSpendSlotsV2_son_ge
      rw [← hpSlots]
      exact hs
    have hwindow' : GrayChargedSpendWindow q a e (pass + 1)
        (core.frozen.map GrayTailRoundV2.toV1 ++ [pV2.toV1]) := by
      apply grayChargedSpendWindowV2_append_round
        (q := q) (L := L) (a := a) (e := e) (pass := pass)
        (U := core.unavailable)
        (server := grayTailLocalServerMove
          (grayChargedSpendDelta a L e pass) core.slots (sm t))
        hpin hspend.pass_lt hwindow hpSlots
      · simpa [hpV2, GrayTailRoundV2.toV1] using hgoal
      · exact hspare
    have hproj : (core.frozen ++ [pV2]).map GrayTailRoundV2.toV1 =
        core.frozen.map GrayTailRoundV2.toV1 ++ [pV2.toV1] := by
      rw [List.map_append, List.map_cons, List.map_nil]
    have hwindowP : GrayChargedSpendWindow q a e (pass + 1)
        ((core.frozen ++ [pV2]).map GrayTailRoundV2.toV1) := by
      rw [hproj]
      exact hwindow'
    by_cases hpass : pass + 1 < 8
    · by_cases hempty :
          (grayChargedSlotsForPassV2 q L a e (pass + 1)
            (core.frozen ++ [pV2])).isEmpty = true
      · have hnil := List.isEmpty_iff.mp hempty
        have hnil' : grayBlockSpendSlotsV2
            (grayChargedSourceCount a e) L (pass + 1)
            (grayChargedThreshold q e) (dyadicScale e)
            (dyadicScale a)
            ((core.frozen ++ [pV2]).map GrayTailRoundV2.toV1) =
            [] := by
          simpa [grayChargedSlotsForPassV2] using hnil
        have hdoneWindow := grayChargedDoneWindowV2_of_slots_nil
          (q := q) (L := L) (a := a) (e := e)
          (pass := pass + 1) hpin hpass hwindowP hnil'
        rw [hpV2] at hempty hdoneWindow
        simpa [grayChargedStepV2, hslots, hgoal, hpass,
          hempty, GrayChargedRequestInvariantV2] using hdoneWindow
      · have hfalse :
            (grayChargedSlotsForPassV2 q L a e (pass + 1)
              (core.frozen ++ [pV2])).isEmpty = false := by
          cases h : (grayChargedSlotsForPassV2 q L a e (pass + 1)
              (core.frozen ++ [pV2])).isEmpty <;> simp_all
        rw [hpV2] at hfalse hwindowP
        simpa [grayChargedStepV2, hslots, hgoal, hpass,
          hfalse, GrayChargedRequestInvariantV2] using hwindowP
    · have hfour : pass + 1 = 8 := by
        have hpassLt : pass < 8 := hspend.pass_lt
        omega
      have hwindow4 : GrayChargedSpendWindow q a e 8
          ((core.frozen ++ [pV2]).map GrayTailRoundV2.toV1) := by
        rw [← hfour]
        exact hwindowP
      have hdoneWindow := grayChargedDoneWindow_of_eight hwindow4
      rw [hpV2] at hdoneWindow
      simpa [grayChargedStepV2, hslots, hgoal, hpass,
        GrayChargedRequestInvariantV2] using hdoneWindow
  · have hgoal_false : grayChargedBlockSpendGoalAtB q L a e pass
        core.slots.length core.unavailable
        (grayBlockSpendMoveV2 q L a e pass sigma core)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          core.slots (sm t)) = false :=
      Bool.eq_false_of_not_eq_true hgoal
    simpa [grayChargedStepV2, hslots, hgoal_false,
      GrayChargedRequestInvariantV2] using hwindow

/-- **The V2 request invariant holds along the run** (pinned gap). -/
theorem grayChargedRequestInvariantV2_stateAt
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e) (t : Nat) :
    GrayChargedRequestInvariantV2 q a e
      (grayChargedRunStateV2
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      simp [GrayChargedRequestInvariantV2, grayChargedRunStateV2,
        grayChargedFoldV2, grayTailServerPrefix, grayChargedInitialStateV2]
  | succ t ih =>
      rw [grayChargedRunStateV2_succ]
      have hcert := grayChargedCertifiedV2_stateAt (n := n)
        q L a e sigma A sm t
      generalize hst : grayChargedRunStateV2
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hcert ih ⊢
      cases hcert with
      | advantage core hcore hsource hactive =>
          have hphase : (grayChargedRunStateV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).phase = .advantage := by rw [hst]
          have hcoreTail' : core = grayChargedBlockTailStateAtV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t := by
            simpa [hst] using grayChargedRunStateV2_core_eq_tailStateAt
              q L a e sigma A sm t hphase
          exact grayChargedRequestInvariantV2_step_advantage hpin hae t core hcoreTail'
      | wait core hcore hsource hdoneCore =>
          have hphase : (grayChargedRunStateV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).phase = .advantage := by rw [hst]
          have hcoreTail' : core = grayChargedBlockTailStateAtV2
              (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t := by
            simpa [hst] using grayChargedRunStateV2_core_eq_tailStateAt
              q L a e sigma A sm t hphase
          exact grayChargedRequestInvariantV2_step_advantage hpin hae t core hcoreTail'
      | done core hdone =>
          have hwindow : GrayChargedDoneWindow q a e
              (core.frozen.map GrayTailRoundV2.toV1) := by
            simpa [GrayChargedRequestInvariantV2] using ih
          simpa [grayChargedStepV2, GrayChargedRequestInvariantV2] using hwindow
      | spend pass core hspend =>
          have hwindow : GrayChargedSpendWindow q a e pass
              (core.frozen.map GrayTailRoundV2.toV1) := by
            simpa [GrayChargedRequestInvariantV2] using ih
          exact grayChargedRequestInvariantV2_step_spend hpin core hspend hwindow

/-- **The V2 final request window** (root H1): at the final time the
displayed root requests sit in `[α/2, α]`. -/
theorem grayChargedV2_final_request_window
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    forall i : Fin n,
      dyadicScale a / 2 <=
          getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm T)
            i.val [] ∧
        getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm T)
            i.val []
          <= dyadicScale a := by
  intro i
  have hdone := grayChargedFinalAtV2_successor_done hfinal
  have hinv := grayChargedRequestInvariantV2_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hpin hae (T + 1)
  have hwindow : GrayChargedDoneWindow q a e
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1) := by
    unfold GrayChargedRequestInvariantV2 at hinv
    rw [hdone] at hinv
    exact hinv
  have hroot := hwindow i
  -- the displayed root at T + 1 is exactly the frozen root request
  have hdisplay : getFamilyReq
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) i.val [] =
      grayChargedFrozenRootRequest q a e
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.map
          GrayTailRoundV2.toV1) i := by
    rw [grayChargedRunMoveV2_root_eq_of_done hdone i]
    rfl
  have hmove := grayChargedFinalAtV2_successor_move_eq hfinal
  rw [← hmove, hdisplay]
  exact hroot

end Kolmogorov
