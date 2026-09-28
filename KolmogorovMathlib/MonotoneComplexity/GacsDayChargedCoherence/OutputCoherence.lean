import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOuterSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTerminationSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.RootIncrements

/-!
# The move the charged run displays is a legal request assignment

Superadditivity over children, entry by entry: `grayChargedEntryMove_nonneg` and
`grayChargedEntryMove_child_le` propagate nonnegativity and the child inequality from single
entries to the move assembled for a slot, and `sum_grayChargedEntryMove_root_le_sonBase` bounds
the root requests of the grandchildren below a son by that son's base. Assembling these gives
`grayCharged_stateAt_entries_coherent` for every entry of a charged state,
`grayCharged_display_source_base_cap` for the source children of the displayed move, and the
conclusion `grayCharged_output_coherentCap`: against a legal server play the charged run displays
a request-coherent move for each client.
-/

namespace Kolmogorov

/-- The move assembled for a slot from nonnegative entries requests a nonnegative amount at every
node. -/
lemma grayChargedEntryMove_nonneg {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hnonneg : ∀ p ∈ entries, ∀ x, 0 ≤ getReq p.2 x)
    (slot : GrayTailSlot n b) (x : GacsDayNode) :
    0 ≤ getReq (grayTailEntryMove entries slot) x := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none => simp [getReq]
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hnonneg pr hmem x

/-- If every entry move is superadditive over children, so is the move assembled for a slot. -/
lemma grayChargedEntryMove_child_le {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hchild : ∀ p ∈ entries, ∀ x,
      getReq p.2 x ≥ ∑ c : Fin b, getReq p.2 (x ++ [c.val]))
    (slot : GrayTailSlot n b) (x : GacsDayNode) :
    getReq (grayTailEntryMove entries slot) x ≥
      ∑ c : Fin b,
        getReq (grayTailEntryMove entries slot) (x ++ [c.val]) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none => simp [getReq]
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hchild pr hmem x

/-- The root requests of the grandchildren below a son `c` sum to at most the son base of `c`. -/
lemma sum_grayChargedEntryMove_root_le_sonBase {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hnonneg : ∀ p ∈ entries, ∀ x, 0 ≤ getReq p.2 x)
    (i : Fin n) (c : Fin b) :
    ∑ c' : Fin b, getReq (grayTailEntryMove entries (i, c, c')) [] ≤
      grayTailSonBase entries i c := by
  induction entries with
  | nil =>
      simp [grayTailEntryMove, grayTailSonBase, getReq]
  | cons p rest ih =>
      rcases p with ⟨⟨i_p, c1_p, c2_p⟩, m_p⟩
      have hp_nonneg : 0 ≤ getReq m_p [] :=
        hnonneg ((i_p, c1_p, c2_p), m_p) (by simp) []
      have hrest_nonneg : ∀ q ∈ rest, ∀ x, 0 ≤ getReq q.2 x :=
        fun q hq x => hnonneg q (by simp [hq]) x
      have hih := ih hrest_nonneg
      have hbase_def : grayTailSonBase rest i c =
          List.foldr (fun p acc =>
            if p.1.1 = i ∧ p.1.2.1 = c then
              getReq p.2 [] + acc else acc) 0 rest := rfl
      rw [hbase_def] at hih
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      by_cases hmatch : i_p = i ∧ c1_p = c
      · rw [if_pos hmatch]
        have h_entry : ∀ c' : Fin b,
            grayTailEntryMove (((i_p, c1_p, c2_p), m_p) :: rest)
                (i, c, c') =
              if c2_p = c' then m_p
              else grayTailEntryMove rest (i, c, c') := by
          intro c'
          unfold grayTailEntryMove
          simp only [List.find?_cons]
          by_cases hc' : c2_p = c'
          · have hslot : (i_p, c1_p, c2_p) = (i, c, c') := by
              ext <;> simp [hmatch.1, hmatch.2, hc']
            rw [if_pos hc']
            simp [hslot]
          · have hslot : (i_p, c1_p, c2_p) ≠ (i, c, c') := by
              intro h
              have : c2_p = c' := by
                injection h with _ h2
                injection h2
              exact hc' this
            rw [if_neg hc']
            simp [hslot]
        simp_rw [h_entry]
        have h_sum :
            (∑ c' : Fin b,
              getReq (if c2_p = c' then m_p
                else grayTailEntryMove rest (i, c, c')) []) =
              getReq m_p [] +
                ∑ c' ∈ Finset.univ.erase c2_p,
                  getReq (grayTailEntryMove rest (i, c, c')) [] := by
          have h_eq :
              (fun c' => getReq (if c2_p = c' then m_p
                else grayTailEntryMove rest (i, c, c')) []) =
              (fun c' => if c2_p = c' then getReq m_p []
                else getReq (grayTailEntryMove rest (i, c, c')) []) := by
            funext c'
            split_ifs <;> rfl
          rw [h_eq, Finset.sum_ite]
          have hfilter :
              Finset.univ.filter (fun c' : Fin b => c2_p = c') =
                {c2_p} := by
            ext x
            simp [eq_comm]
          have hfilter_ne :
              Finset.univ.filter (fun c' : Fin b => ¬c2_p = c') =
                Finset.univ.erase c2_p := by
            ext x
            simp [ne_comm]
          rw [hfilter, hfilter_ne, Finset.sum_singleton]
        rw [h_sum]
        have h_sub :
            (∑ c' ∈ Finset.univ.erase c2_p,
              getReq (grayTailEntryMove rest (i, c, c')) []) ≤
            ∑ c' : Fin b,
              getReq (grayTailEntryMove rest (i, c, c')) [] := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) ?_
          intro c' _ _
          exact grayChargedEntryMove_nonneg rest hrest_nonneg
            (i, c, c') []
        linarith
      · rw [if_neg hmatch]
        have h_entry : ∀ c' : Fin b,
            grayTailEntryMove (((i_p, c1_p, c2_p), m_p) :: rest)
                (i, c, c') =
              grayTailEntryMove rest (i, c, c') := by
          intro c'
          unfold grayTailEntryMove
          simp only [List.find?_cons]
          have hslot : (i_p, c1_p, c2_p) ≠ (i, c, c') := by
            intro h
            apply hmatch
            injection h with h1 h2
            injection h2 with h3 h4
            exact ⟨h1, h3⟩
          simp [hslot]
        simp_rw [h_entry]
        exact hih

/-- Against a legal server play, every entry of a charged state — frozen, slot or current — is
request coherent with cap `dyadicScale (grayChargedSpendAlphaDepth a)`. -/
theorem grayCharged_stateAt_entries_coherent
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let current : FamilyClientMove := match st.phase with
      | .done => []
      | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core
    ∀ pr ∈ grayTailEntries st.core.frozen st.core.slots current,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a)) pr.2 := by
  dsimp only
  let st := grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let current : FamilyClientMove := match st.phase with
    | .done => []
    | .advantage => if st.core.slots.isEmpty then []
      else grayTailCurrentMove q L e sigma st.core
    | .spend pass => if st.core.slots.isEmpty then []
      else grayChargedSpendMove q L a e pass sigma st.core
  have hfrozen := grayChargedFrozenCoherent_stateAt
    (t := t) ha hae hroom hB hRung hsm
  have hstateCurrent := grayChargedCurrentMove_stateAt_coherent
    (t := t) ha hae hB hRung hsm
  have hstateSpend := grayChargedSpendMove_stateAt_coherent
    (t := t) hroom hB hRung hsm
  have hcurrent : ∀ j < st.core.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt current j) := by
    intro j hj
    cases hphase : st.phase with
    | done =>
        simp [current, hphase, requestCoherentCap,
          familyClientMoveAt, getReq,
          (dyadicScale_pos (grayChargedSpendAlphaDepth a)).le]
    | advantage =>
        have hne : 1 <= st.core.slots.length := by omega
        have hempty : st.core.slots.isEmpty = false := by
          cases hs : st.core.slots with
          | nil => simp [hs] at hj
          | cons x xs => simp
        have hcoh := (hstateCurrent hphase hne j hj).mono_cap
          (grayChargedCallScale_le_spendAlpha hae)
        simpa [current, hphase, hempty, st] using hcoh
    | spend pass =>
        have hne : 1 <= st.core.slots.length := by omega
        have hempty : st.core.slots.isEmpty = false := by
          cases hs : st.core.slots with
          | nil => simp [hs] at hj
          | cons x xs => simp
        have hcoh := hstateSpend pass hphase hne j hj
        simpa [current, hphase, hempty, st] using hcoh
  intro pr hpr
  rw [grayTailEntries, List.mem_append] at hpr
  rcases hpr with hpr | hpr
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hpr
    obtain ⟨p, hp, hpr⟩ := hpr
    rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst pr
    exact hfrozen p hp j.val j.isLt
  · rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst pr
    exact hcurrent j.val j.isLt

/-- Against a legal server play, the son base of every source child of the displayed move stays
at most `dyadicScale e`. -/
theorem grayCharged_display_source_base_cap
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : c.val < grayChargedSourceCount a e) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let current : FamilyClientMove := match st.phase with
      | .done => []
      | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core
    grayTailSonBase
        (grayTailEntries st.core.frozen st.core.slots current) i c <=
      dyadicScale e := by
  dsimp only
  have hsourceCap := grayChargedSourceBaseCap_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) (t := t)
  have hcurrent := grayChargedCurrentMove_stateAt_coherent
    (t := t) ha hae hB hRung hsm
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hsourceCap hcurrent hcert ⊢
  cases hcert with
  | advantage core hcore hsource hactive =>
      have hphase :
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).phase = .advantage := by
        rw [hst]
      have hcoreTail := grayChargedStateAt_core_eq_tailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t (by simp [hst])
      have hcoreTail' : core = grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t := by
        simpa [hst] using hcoreTail
      have hactiveBase := grayChargedTail_active_base_le_stateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t
      rw [← hcoreTail'] at hactiveBase
      by_cases hempty : core.slots.isEmpty
      · have hnil : core.slots = [] := List.isEmpty_iff.mp hempty
        simpa [hnil, grayTailEntries, grayTailSlotEntries,
          grayTailSonBase] using hsourceCap i c hc
      · have hne : 1 <= core.slots.length := by
          cases hs : core.slots with
          | nil => simp [hs] at hempty
          | cons x xs => exact Nat.succ_pos _
        have hcur := hcurrent (by simp) hne
        have hslotBase :
            grayTailSonBase
                (grayTailSlotEntries core.slots
                  (grayTailCurrentMove q L e sigma core)) i c <=
              dyadicScale (grayCallDepth q e) := by
          apply grayTailSonBase_le_of_slot_request_bounds
            (dyadicScale_pos _).le hcore.shape.slots_nodup
              hcore.shape.slots_round
          · intro j
            exact (hcur j.val j.isLt).1 []
          · intro j
            exact (hcur j.val j.isLt).2.1
        simp only [hempty, Bool.false_eq_true, if_false]
        rw [grayTailEntries, grayTailSonBase_append_globalEntries]
        by_cases hhas : GrayTailHasKey core.slots i c
        · obtain ⟨s, hs, hi, hc'⟩ := hhas
          have hfrozen : grayTailFrozenSonBase core.frozen i c <=
              grayChargedThreshold q e := by
            simpa [hi, hc'] using hactiveBase s hs
          exact le_trans (add_le_add hfrozen hslotBase) (by
            simpa [grayChargedThreshold] using
              grayTail_callScale_add_threshold_le q e)
        · have hzero :
              grayTailSonBase
                (grayTailSlotEntries core.slots
                  (grayTailCurrentMove q L e sigma core)) i c = 0 :=
            grayTailSonBase_eq_zero_of_not_hasKey i c hhas
          rw [hzero, add_zero]
          exact hsourceCap i c hc
  | spend pass core hspend =>
      have hempty : core.slots.isEmpty = false := hspend.slots_nonempty
      have hzero :
          grayTailSonBase
            (grayTailSlotEntries core.slots
              (grayChargedSpendMove q L a e pass sigma core)) i c = 0 := by
        apply grayTailSonBase_eq_zero_of_no_match
        intro z hz
        rw [grayTailSlotEntries, List.mem_ofFn] at hz
        obtain ⟨j, rfl⟩ := hz
        right
        intro heq
        have hmem : core.slots.get j ∈
            grayChargedSlotsForPass q a e pass core.frozen := by
          rw [← hspend.slots_eq]
          exact List.get_mem _ _
        have hge : grayChargedSourceCount a e <=
            (core.slots.get j).2.1.val :=
          grayChargedSpendSlots_son_ge
            (by simpa [grayChargedSlotsForPass] using hmem)
        have hval : (core.slots.get j).2.1.val = c.val :=
          congrArg Fin.val heq
        omega
      simp only [hempty, Bool.false_eq_true, if_false]
      rw [grayTailEntries, grayTailSonBase_append_globalEntries, hzero, add_zero]
      exact hsourceCap i c hc
  | done core hdone =>
      simpa [grayTailEntries, hdone.slots_empty,
        grayTailSlotEntries, grayTailSonBase] using hsourceCap i c hc

/-- Against a legal server play, the move the charged run displays for each client is request
coherent with cap `dyadicScale a`. -/
theorem grayCharged_output_coherentCap
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (i : Nat) (hi : i < n) :
    requestCoherentCap (grayTailBranch q L a e) (dyadicScale a)
      (familyClientMoveAt
        (grayChargedDisplayedMove q L a e sigma
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t)) i) := by
  let b := grayTailBranch q L a e
  let st := grayChargedStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let current : FamilyClientMove := match st.phase with
    | .done => []
    | .advantage => if st.core.slots.isEmpty then []
      else grayTailCurrentMove q L e sigma st.core
    | .spend pass => if st.core.slots.isEmpty then []
      else grayChargedSpendMove q L a e pass sigma st.core
  let entries := grayTailEntries st.core.frozen st.core.slots current
  have hentries_coh : ∀ pr ∈ entries,
      requestCoherentCap b
        (dyadicScale (grayChargedSpendAlphaDepth a)) pr.2 := by
    simpa [st, current, entries, b] using
      (grayCharged_stateAt_entries_coherent
        (t := t) ha hae hroom hB hRung hsm)
  have hentries_nonneg : ∀ pr ∈ entries, ∀ x, 0 <= getReq pr.2 x := by
    intro pr hpr x
    exact (hentries_coh pr hpr).1 x
  have hentries_child : ∀ pr ∈ entries, ∀ x,
      getReq pr.2 x >= ∑ c : Fin b, getReq pr.2 (x ++ [c.val]) := by
    intro pr hpr x
    exact (hentries_coh pr hpr).2.2 x
  have hsourceCap (c : Fin b)
      (hc : c.val < grayChargedSourceCount a e) :
      grayTailSonBase entries ⟨i, hi⟩ c <= dyadicScale e := by
    simpa [st, current, entries, b] using
      (grayCharged_display_source_base_cap
        (t := t) ha hae hB hRung hsm ⟨i, hi⟩ c hc)
  have hson_nonneg (c : Fin b) :
      0 <= grayChargedSonRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) entries ⟨i, hi⟩ c := by
    unfold grayChargedSonRequest
    by_cases hc : c.val < grayChargedSourceCount a e
    · rw [if_pos hc]
      unfold grayTailSonRequest
      by_cases hlarge : grayChargedThreshold q e <
          grayTailSonBase entries ⟨i, hi⟩ c
      · rw [if_pos hlarge]
        exact (dyadicScale_pos e).le
      · rw [if_neg hlarge]
        exact grayTailSonBase_nonneg_global
          (fun pr hpr => hentries_nonneg pr hpr [])
    · rw [if_neg hc]
      exact grayTailSonBase_nonneg_global
        (fun pr hpr => hentries_nonneg pr hpr [])
  have hbase_le_son (c : Fin b) :
      grayTailSonBase entries ⟨i, hi⟩ c <=
        grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries ⟨i, hi⟩ c := by
    by_cases hc : c.val < grayChargedSourceCount a e
    · rw [grayChargedSonRequest_source _ _ hc]
      unfold grayTailSonRequest
      by_cases hlarge : grayChargedThreshold q e <
          grayTailSonBase entries ⟨i, hi⟩ c
      · rw [if_pos hlarge]
        exact hsourceCap c hc
      · rw [if_neg hlarge]
    · rw [grayChargedSonRequest_spare _ _ (Nat.le_of_not_gt hc)]
  have hrootcap :
      grayChargedRootRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries ⟨i, hi⟩ <= dyadicScale a := by
    simpa [st, current, entries, b] using
      (grayCharged_display_root_cap
        (t := t) ha hae hroom hB hRung hsm ⟨i, hi⟩)
  change requestCoherentCap b (dyadicScale a)
    (familyClientMoveAt
      (grayChargedTailFamilyMove
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) st.core.frozen st.core.slots current) i)
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hi]
  refine requestCoherentCap_graftTwoLevel
    ?hroot0 ?hcap ?hson0 ?hsum ?hsonsum ?hpos ?hchild
  · unfold grayChargedRootRequest
    exact Finset.sum_nonneg fun c _ => hson_nonneg c
  · exact hrootcap
  · intro c hc
    dsimp only
    rw [dif_pos hc]
    exact hson_nonneg ⟨c, hc⟩
  · have hsum_eq :
        (∑ c : Fin b, if hc : c.val < b then
          grayChargedSonRequest
            (grayChargedSourceCount a e) (grayChargedThreshold q e)
            (dyadicScale e) entries ⟨i, hi⟩ ⟨c.val, hc⟩ else 0) =
        ∑ c : Fin b,
          grayChargedSonRequest
            (grayChargedSourceCount a e) (grayChargedThreshold q e)
            (dyadicScale e) entries ⟨i, hi⟩ c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dif_pos c.isLt]
    rw [hsum_eq]
    exact le_rfl
  · intro c hc
    dsimp only
    rw [dif_pos hc]
    have hsum := (sum_grayChargedEntryMove_root_le_sonBase
      entries hentries_nonneg ⟨i, hi⟩ ⟨c, hc⟩).trans
        (hbase_le_son ⟨c, hc⟩)
    refine le_trans (le_of_eq ?_) hsum
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [dif_pos hc, dif_pos c'.isLt]
  · intro c hc c' hc' x
    dsimp only
    rw [dif_pos hc, dif_pos hc']
    exact grayChargedEntryMove_nonneg entries hentries_nonneg
      (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x
  · intro c hc c' hc' x
    dsimp only
    rw [dif_pos hc, dif_pos hc']
    exact grayChargedEntryMove_child_le entries hentries_child
      (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x

end Kolmogorov
