import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafD
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntrySupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.FrozenCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity

/-!
# The tail never displays a tiny request

`requestAvoidsSmall` asks that every positive request of a move be at least a given scale;
keeping it is what makes the displayed play usable by the outer game. The structural step is
`requestAvoidsSmall_graftTwoLevel` for a two-level graft, from which the property is propagated
to the current move (`grayTailCurrentMove_avoidsSmall`), to the move assembled for a slot
(`grayTail_entryMove_avoidsSmall`), to all entries (`grayTailEntries_all_avoidsSmall`) and — as
the invariant `GrayTailFrozenAvoidsSmall`, preserved by `grayTailFrozenAvoidsSmall_step` — to the
frozen rounds. The conclusion is `grayTail_output_avoidsSmall`: every displayed positive request
is at least the fine scale.
-/

namespace Kolmogorov
open scoped BigOperators

/-- Structural helper: a two-level graft satisfies `requestAvoidsSmall` if its root,
sons, and recursive entries satisfy `requestAvoidsSmall`. -/
theorem requestAvoidsSmall_graftTwoLevel {b : ℕ} {root delta : ℚ} {son : ℕ → ℚ}
    {g : ℕ → ℕ → ClientMove}
    (hroot : root = 0 ∨ delta ≤ root)
    (hson : ∀ c < b, son c = 0 ∨ delta ≤ son c)
    (hg : ∀ c < b, ∀ c' < b, requestAvoidsSmall delta (g c c')) :
    requestAvoidsSmall delta (graftTwoLevel root b son g) := by
  intro x
  cases x with
  | nil =>
      rw [getReq_graftTwoLevel_root]
      exact hroot
  | cons c x =>
      cases x with
      | nil =>
          by_cases hc : c < b
          · rw [getReq_graftTwoLevel_son hc]
            exact hson c hc
          · push_neg at hc
            rw [getReq_graftTwoLevel_of_ge hc]
            exact Or.inl rfl
      | cons c' y =>
          by_cases hc : c < b
          · by_cases hc' : c' < b
            · rw [getReq_graftTwoLevel_grandson hc hc']
              exact hg c hc c' hc' y
            · push_neg at hc'
              rw [getReq_graftTwoLevel_of_son_ge hc hc']
              exact Or.inl rfl
          · push_neg at hc
            rw [getReq_graftTwoLevel_of_ge hc]
            exact Or.inl rfl

/-- Along a certified run against a legal server play, the current move requests nothing below
`dyadicScale (e + grayTailNewLoss q L)`. -/
lemma grayTailCurrentMove_avoidsSmall
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hactive : ((grayTailStateAt (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).done ||
        (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) ≠ true) :
    familyRequestAvoidsSmall
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayTailCurrentMove q L e sigma
        (grayTailStateAt (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t)) := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t with hst
  have hcert : GrayTailCertified q L e A sm t st :=
    grayTailCertified_stateAt _ _ _ _ _ _ _ _
  have hhist : GrayTailHistoryOK q L e sigma st :=
    grayTailHistoryOK_stateAt _ _ _ _ _ _ _ _
  have htrace : GrayTailTrace q L e sm t st :=
    grayTailTrace_stateAt _ _ _ _ _ _ _ _
  have hround : st.frozen.length < grayTailRoundCount q := by
    by_contra h
    push_neg at h
    have hcount : grayTailRoundCount q ≤
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).frozen.length := by
      rw [← hst]
      exact h
    have hdone := grayTail_done_of_roundCount_stateAt_core
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) (t := t) hcount
    rw [← hst] at hdone
    rw [hdone] at hactive
    contradiction
  have hlocal := grayTailFutureServer_legal hcert hround hsm
  have hb : grayTailBaseBranch q L ≤ grayTailBranch q L a e := by
    exact le_max_right _ _
  have hmin := (grayTailRound_gameSpec ha hae hB hRung hcert hactive hb).weak.minimum_request
    (grayTailFutureServer q L e st sm) hlocal st.history.2.length
  rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
  intro j hj x
  rcases hmin j hj x with h0 | hge
  · exact Or.inl h0
  · have hdelta_raw := grayTailRoundDelta_upper q L e st.frozen.length
    have hdelta_le :
        grayTailRoundDelta q L e st.frozen.length ≤ e + grayTailNewLoss q L := by
      simpa only [grayTailNewLoss, Nat.add_assoc] using hdelta_raw
    have hscale := dyadicScale_antitone hdelta_le
    exact Or.inr (le_trans hscale hge)

/-- A move assembled for a slot from entries that avoid small requests again avoids them. -/
lemma grayTail_entryMove_avoidsSmall {n b : ℕ} {delta : ℚ}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (slot : GrayTailSlot n b) :
    requestAvoidsSmall delta (grayTailEntryMove entries slot) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none =>
      intro x
      simp [getReq]
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hall pr hmem

/-- If the frozen moves and the current move avoid requests below `delta`, so does every entry. -/
lemma grayTailEntries_all_avoidsSmall {n b : ℕ} {delta : ℚ}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hfrozen : ∀ p ∈ frozen, ∀ j < p.slots.length,
      requestAvoidsSmall delta (familyClientMoveAt p.move j))
    (hcur : ∀ j < slots.length,
      requestAvoidsSmall delta (familyClientMoveAt current j)) :
    ∀ pr ∈ grayTailEntries frozen slots current,
      requestAvoidsSmall delta pr.2 := by
  intro pr hpr
  rw [grayTailEntries, List.mem_append] at hpr
  rcases hpr with hpr | hpr
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hpr
    obtain ⟨p, hp, hpr⟩ := hpr
    rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hfrozen p hp j.val j.isLt
  · rw [grayTailSlotEntries, List.mem_ofFn] at hpr
    obtain ⟨j, hj⟩ := hpr
    subst hj
    exact hcur j.val j.isLt

/-- Every move recorded in the frozen rounds avoids requests below
`dyadicScale (e + grayTailNewLoss q L)`. -/
def GrayTailFrozenAvoidsSmall {n b : ℕ} (q L e : ℕ) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L)) (familyClientMoveAt p.move j)

/-- A tail step keeps the frozen rounds free of small requests. -/
lemma grayTailFrozenAvoidsSmall_step
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hst_frozen : GrayTailFrozenAvoidsSmall q L e
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen) :
    GrayTailFrozenAvoidsSmall q L e
      (grayTailStep q L a e sigma A
        (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)
        (sm t)).frozen := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t with hst
  rw [grayTailStep_eq]
  by_cases hactive : st.done || st.slots.isEmpty
  · simpa [hactive] using hst_frozen
  · simp only [hactive, Bool.false_eq_true, if_false]
    by_cases hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots (sm t))
    · simp only [hgoal, if_true]
      intro p hp j hj
      rcases List.mem_append.mp hp with hp | hp
      · exact hst_frozen p hp j hj
      · simp only [List.mem_singleton] at hp
        subst hp
        exact grayTailCurrentMove_avoidsSmall ha hae hB hRung hsm hactive j hj
    · simp only [hgoal]
      exact hst_frozen

/-- At every time of a tail run the frozen rounds avoid requests below the fine scale. -/
lemma grayTailFrozenAvoidsSmall_stateAt
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    GrayTailFrozenAvoidsSmall q L e
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen := by
  induction t with
  | zero =>
      intro p hp
      simp [grayTailStateAt_zero, grayTailInitialState] at hp
  | succ t ih =>
      rw [grayTailStateAt_succ]
      exact grayTailFrozenAvoidsSmall_step ha hae hB hRung hsm ih

/-- Every displayed entry of a tail run avoids requests below
`dyadicScale (e + grayTailNewLoss q L)`. -/
theorem grayTail_stateAt_entries_avoidsSmall
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (pr : GrayTailSlot n (grayTailBranch q L a e) × ClientMove)
    (hpr : pr ∈ grayTailOutputEntries q L e sigma
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)) :
    requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L)) pr.2 := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hfrozen := grayTailFrozenAvoidsSmall_stateAt ha hae hB hRung hsm (t := t)
  refine grayTailEntries_all_avoidsSmall hfrozen ?_ pr hpr
  intro j hj
  by_cases hdone : st.done
  · rw [hdone]
    intro x
    simp [getReq, familyClientMoveAt]
  · have hdone_eq : st.done = false := Bool.eq_false_of_not_eq_true hdone
    rw [hdone_eq]
    by_cases hempty : st.slots.isEmpty
    · have hlen : st.slots.length = 0 := List.isEmpty_iff_length_eq_zero.mp hempty
      omega
    · have hact : (st.done || st.slots.isEmpty) = false := by
        simp [hdone_eq, hempty]
      have hactive : (st.done || st.slots.isEmpty) ≠ true := by
        rw [hact]
        decide
      exact grayTailCurrentMove_avoidsSmall ha hae hB hRung hsm hactive j hj

/-- A son base built from entries that avoid small requests is either `0` or at least `delta`. -/
lemma grayTailSonBase_avoidsSmall {n b : ℕ} {delta : ℚ}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hpos_delta : 0 < delta)
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase entries i c = 0 ∨ delta ≤ grayTailSonBase entries i c := by
  induction entries with
  | nil =>
      simp [grayTailSonBase]
  | cons p rest ih =>
      have hhead : requestAvoidsSmall delta p.2 := hall p (by simp)
      have htail : ∀ pr ∈ rest, requestAvoidsSmall delta pr.2 :=
        fun pr hpr => hall pr (by simp [hpr])
      have ih_res := ih htail
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      change
        (if p.1.1 = i ∧ p.1.2.1 = c then
            getReq p.2 [] + grayTailSonBase rest i c
          else grayTailSonBase rest i c) = 0 ∨
        delta ≤ (if p.1.1 = i ∧ p.1.2.1 = c then
          getReq p.2 [] + grayTailSonBase rest i c else grayTailSonBase rest i c)
      split_ifs with hmatch
      · rcases hhead [] with h0 | hge
        · rw [h0, zero_add]
          exact ih_res
        · rcases ih_res with h0' | hge'
          · rw [h0', add_zero]
            exact Or.inr hge
          · have hnonneg : 0 ≤ grayTailSonBase rest i c := by
              rcases hge' with _
              linarith
            have hsum : delta ≤ getReq p.2 [] + grayTailSonBase rest i c := by linarith
            exact Or.inr hsum
      · exact ih_res

/-- A son request built from entries that avoid small requests is either `0` or at least `delta`. -/
lemma grayTailSonRequest_avoidsSmall {n b : ℕ} {e : ℕ} {delta : ℚ}
    (hpos_delta : 0 < delta)
    (hae : delta ≤ dyadicScale e)
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (threshold : ℚ) (i : Fin n) (c : Fin b) :
    grayTailSonRequest threshold (dyadicScale e) entries i c = 0 ∨
      delta ≤ grayTailSonRequest threshold (dyadicScale e) entries i c := by
  unfold grayTailSonRequest
  by_cases htr : threshold < grayTailSonBase entries i c
  · dsimp only
    rw [if_pos htr]
    exact Or.inr hae
  · dsimp only
    rw [if_neg htr]
    exact grayTailSonBase_avoidsSmall hpos_delta hall i c

/-- A root request built from entries that avoid small requests is either `0` or at least
`delta`, the target floor included. -/
lemma grayTailRootRequest_avoidsSmall {n b q a e : ℕ} {delta : ℚ}
    (hpos_delta : 0 < delta)
    (_ha : 1 ≤ a) (_hae : a ≤ e) (hfloor : delta ≤ grayTailTargetFloor q a)
    (hdelta_e : delta ≤ dyadicScale e)
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2)
    (done : Bool) (threshold : ℚ) (i : Fin n) :
    grayTailRootRequest done (grayTailTargetFloor q a) threshold (dyadicScale e) entries i = 0 ∨
      delta
        ≤ grayTailRootRequest done (grayTailTargetFloor q a) threshold (dyadicScale e) entries i :=
        by
  unfold grayTailRootRequest
  have hson_avoids : ∀ c : Fin b,
      grayTailSonRequest threshold (dyadicScale e) entries i c = 0 ∨
        delta ≤ grayTailSonRequest threshold (dyadicScale e) entries i c :=
    fun c => grayTailSonRequest_avoidsSmall hpos_delta hdelta_e hall threshold i c
  have hsum_avoids : (∑ c : Fin b, grayTailSonRequest threshold (dyadicScale e) entries i c) = 0 ∨
      delta ≤ (∑ c : Fin b, grayTailSonRequest threshold (dyadicScale e) entries i c) := by
    by_cases hpos : 0 < ∑ c : Fin b, grayTailSonRequest threshold (dyadicScale e) entries i c
    · exact Or.inr (sum_ge_of_forall_zero_or_ge Finset.univ _ delta hpos (fun c _ => hson_avoids c))
    · have hnonneg : ∀ c : Fin b, 0 ≤ grayTailSonRequest threshold (dyadicScale e) entries i c := by
        intro c
        rcases hson_avoids c with h0 | hge
        · rw [h0]
        · linarith
      have hsum_nonneg : 0 ≤ ∑ c : Fin b,
        grayTailSonRequest threshold (dyadicScale e) entries i c :=
        Finset.sum_nonneg (fun c _ => hnonneg c)
      exact Or.inl (by linarith)
  by_cases hd : done
  · dsimp only
    rw [if_pos hd]
    exact Or.inr (le_trans hfloor (le_max_right _ _))
  · dsimp only
    rw [if_neg hd]
    exact hsum_avoids

/-- **Child E5g.**  Every displayed positive request is at least the fine
scale `dyadicScale (e + grayTailNewLoss q L)`.

The grandson requests are the recursive ones, which avoid small values at their
own round scale `grayTailRoundDelta q L e r ≤ e + grayTailNewLoss q L`; a son
request is either such a finite sum or `dyadicScale e`; a root request is a sum
of son requests or the positive floor `grayTailTargetFloor q a`. -/
theorem grayTail_output_avoidsSmall
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : ℕ) :
    familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ (e + grayTailNewLoss q L))
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm t) := by
  intro i hi
  have hplay := playClientFamily_grayTailStrategy q L a e n sigma A sm t
  have hcm := familyClientMoveAt_grayTailOutput (q := q) (L := L) (a := a) (e := e) (sigma := sigma)
    (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t) hi
  rw [hplay, hcm]
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  set delta := dyadicScale (e + grayTailNewLoss q L)
  set entries := grayTailOutputEntries q L e sigma st
  set threshold := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
  set eps := dyadicScale e
  have hall : ∀ pr ∈ entries, requestAvoidsSmall delta pr.2 :=
    fun pr hpr => grayTail_stateAt_entries_avoidsSmall ha hae hB hRung hsm pr hpr
  have hdelta_e : delta ≤ eps := dyadicScale_antitone (by omega)
  have hfloor : delta ≤ grayTailTargetFloor q a := grayTailTargetFloor_avoidsSmall q L a e ha hae
  refine requestAvoidsSmall_graftTwoLevel ?hroot ?hson ?hg
  · exact grayTailRootRequest_avoidsSmall (dyadicScale_pos
                                            _) ha hae hfloor hdelta_e hall st.done threshold ⟨i, hi⟩
  · intro c hc
    dsimp only
    rw [dif_pos hc]
    exact grayTailSonRequest_avoidsSmall (dyadicScale_pos _) hdelta_e hall threshold
      ⟨i, hi⟩ ⟨c, hc⟩
  · intro c hc c' hc'
    dsimp only
    rw [dif_pos hc, dif_pos hc']
    exact grayTail_entryMove_avoidsSmall hall (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩)

end Kolmogorov
