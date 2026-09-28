import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProgressStrict

/-!
# Strict V2 base-le chain (toV1-threaded) — the budget side of progress

The frozen son-base of the strict V2 state stays `≤ dyadicScale e`, so the
frozen request sum is bounded by the source budget.  The son increment of an
accepted wide-block round is bounded by the record-agnostic son-base keystone
`grayChargedBlockRoundSonBase_le_callScale`.
-/

namespace Kolmogorov

/-- V1 view of a V2 state's frozen list. -/
def frozenV1OfV2 {n b : ℕ} (st : GrayTailStateV2 n b) : GrayTailFrozen n b :=
  st.frozen.map GrayTailRoundV2.toV1

/-- Active-slots base bound preserved by the strict step. -/
lemma grayChargedBlockV2_active_base_le_step {n q L a e : Nat}
    (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n (grayTailBranch q L a e)) (sm : FamilyServerMove)
    (hprev : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase (frozenV1OfV2 st) s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall s, s ∈ (grayChargedBlockTailStepV2 q L a e sigma A st sm).slots ->
      grayTailFrozenSonBase
          (frozenV1OfV2 (grayChargedBlockTailStepV2 q L a e sigma A st sm)) s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  by_cases hd : st.done = true
  · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
        { st with time := st.time + 1 } := by simp [grayChargedBlockTailStepV2, hd]
    rw [hstep]; exact hprev
  · by_cases hs : st.slots.isEmpty = true
    · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with time := st.time + 1 } := by simp [grayChargedBlockTailStepV2, hd, hs]
      rw [hstep]; exact hprev
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStepV2, hd, hs, hg, Bool.false_eq_true, ↓reduceIte]
        intro s hs'
        exact grayBlockNextSlots_base_le_global hs'
      · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with
            time := st.time + 1
            history :=
              (st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st],
                st.history.2 ++ [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length) st.slots sm]) } := by
          simp [grayChargedBlockTailStepV2, hd, hs, hg]
        rw [hstep]; exact hprev

/-- At every time of a V2 block tail run, every open slot is below the service threshold. -/
theorem grayChargedBlockV2_active_base_le_stateAt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall s, s ∈ (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).slots ->
      grayTailFrozenSonBase
          (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm t)) s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
  induction t with
  | zero =>
      intro s hs
      simp only [grayChargedBlockTailStateAtV2, grayChargedBlockTailFoldV2,
        grayChargedBlockTailInitialStateV2, frozenV1OfV2,
        grayTailFrozenSonBase, grayTailFrozenEntries] at *
      simpa [grayTailSonBase] using grayTail_threshold_nonneg_global q e
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockV2_active_base_le_step sigma A _ (sm t) ih

/-- A V2 block tail step keeps every frozen son base below `dyadicScale e`. -/
lemma grayChargedBlockV2_all_frozen_base_le_step {n q L a e : Nat}
    (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n (grayTailBranch q L a e)) (sm : FamilyServerMove)
    (hshape : GrayBlockTailShapeV2 q L st)
    (hprev : forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      grayTailFrozenSonBase (frozenV1OfV2 st) i c <= dyadicScale e)
    (hactive : forall s, s ∈ st.slots ->
      grayTailFrozenSonBase (frozenV1OfV2 st) s.1 s.2.1 <=
        dyadicScale e - dyadicScale e / (6 * halfAmplification q)) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      grayTailFrozenSonBase
        (frozenV1OfV2 (grayChargedBlockTailStepV2 q L a e sigma A st sm)) i c <=
          dyadicScale e := by
  by_cases hd : st.done = true
  · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
        { st with time := st.time + 1 } := by simp [grayChargedBlockTailStepV2, hd]
    rw [hstep]; exact hprev
  · by_cases hs : st.slots.isEmpty = true
    · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with time := st.time + 1 } := by simp [grayChargedBlockTailStepV2, hd, hs]
      rw [hstep]; exact hprev
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStepV2, hd, hs, hg, Bool.false_eq_true, ↓reduceIte]
        intro i c
        simp only [frozenV1OfV2, List.map_append, List.map_cons, List.map_nil,
          GrayTailRoundV2.toV1]
        rw [grayTailFrozenSonBase_append_global]
        by_cases hson : GrayTailHasKey st.slots i c
        · obtain ⟨sl, hsl, hi, hc⟩ := hson
          have hold : grayTailFrozenSonBase (frozenV1OfV2 st) i c <=
              dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
            simpa [hi, hc] using hactive sl hsl
          have hnew := grayChargedBlockRoundSonBase_le_callScale
            (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (e := e)
            (r := st.frozen.length) (A := st.unavailable)
            (slots := st.slots) (move := grayBlockCurrentMoveV2 q L e sigma st)
            (server := grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
            hg
            (fun i c => grayInAdvBlock_fibre_count_le hshape.slots_nodup
              hshape.slots_range i c) i c
          have hcombine := le_trans (add_le_add hold hnew)
            (grayTail_callScale_add_threshold_le q e)
          simpa [frozenV1OfV2] using hcombine
        · rw [grayTailSonBase_eq_zero_of_not_hasKey i c hson, add_zero]
          have hp := hprev i c
          simpa [frozenV1OfV2] using hp
      · have hstep : grayChargedBlockTailStepV2 q L a e sigma A st sm =
          { st with
            time := st.time + 1
            history :=
              (st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st],
                st.history.2 ++ [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length) st.slots sm]) } := by
          simp [grayChargedBlockTailStepV2, hd, hs, hg]
        rw [hstep]; exact hprev

/-- At every time of a V2 block tail run, every frozen son base is at most `dyadicScale e`. -/
theorem grayChargedBlockV2_all_frozen_base_le_stateAt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    forall (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      grayTailFrozenSonBase
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t)) i c <= dyadicScale e := by
  induction t with
  | zero =>
      intro i c
      simp [grayChargedBlockTailStateAtV2, grayChargedBlockTailFoldV2,
        grayChargedBlockTailInitialStateV2, frozenV1OfV2, grayTailFrozenSonBase,
        grayTailFrozenEntries, grayTailSonBase, (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      apply grayChargedBlockV2_all_frozen_base_le_step sigma A _ (sm t)
        (grayChargedBlockTailCertifiedV2_stateAt q L a e sigma A sm t).shape ih
      exact grayChargedBlockV2_active_base_le_stateAt q L a e sigma A sm t

/-- V2 frozen entries use source sons `< 2^{e-a}`. -/
lemma grayChargedBlockV2_frozenEntries_used {n q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {t : Nat} {z : GrayTailSlot n (grayTailBranch q L a e) × ClientMove}
    (hz : z ∈ grayTailFrozenEntries
      (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t))) :
    z.1.2.1.val < 2 ^ (e - a) := by
  unfold grayTailFrozenEntries frozenV1OfV2 at hz
  rw [List.flatMap_map, List.mem_flatMap] at hz
  obtain ⟨q0, hq0, hz⟩ := hz
  simp only [GrayTailRoundV2.toV1, grayTailSlotEntries] at hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hsource := (grayChargedBlockSourceInvariantV2_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen q0 hq0
  have hmem := hsource (q0.slots.get j) (List.get_mem q0.slots j)
  simpa [grayChargedSourceCount] using hmem

/-- The V2 source-base sum equals the request sum (via the source invariant). -/
lemma grayChargedBlockV2_frozenSourceBaseSum_eq {n q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {t : Nat} :
    grayTailFrozenSourceBaseSum (2 ^ (e - a))
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t)) =
      grayTailFrozenRequestSum
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t)) := by
  rw [grayTailFrozenRequestSum_eq_entries]
  unfold grayTailFrozenSourceBaseSum grayTailFrozenSonBase
  apply grayTailSourceBaseSum_eq_entryRequestSum
  intro z hz
  exact grayChargedBlockV2_frozenEntries_used hz

/-- **The V2 frozen request sum is bounded by the source budget.** -/
theorem grayChargedBlockV2_frozenRequestSum_le_source_budget {n q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {t : Nat} :
    grayTailFrozenRequestSum
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t)) <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
  rw [← grayChargedBlockV2_frozenSourceBaseSum_eq]
  unfold grayTailFrozenSourceBaseSum
  have hbase := grayChargedBlockV2_all_frozen_base_le_stateAt (n := n) q L a e sigma A sm t
  have hinner : forall i : Fin n,
      (∑ c : Fin (grayTailBranch q L a e),
        if c.val < 2 ^ (e - a) then
          grayTailFrozenSonBase
            (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
              (b := grayTailBranch q L a e) q L a e sigma A sm t)) i c else 0) <=
        ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
    intro i
    calc
      (∑ c : Fin (grayTailBranch q L a e),
          if c.val < 2 ^ (e - a) then
            grayTailFrozenSonBase _ i c else 0) =
          ∑ c ∈ Finset.univ.filter (fun c : Fin (grayTailBranch q L a e) => c.val < 2 ^ (e - a)),
              grayTailFrozenSonBase _ i c := by rw [Finset.sum_filter]
      _ <= ∑ _c ∈ Finset.univ.filter (fun c : Fin (grayTailBranch q L a e) => c.val < 2 ^ (e - a)),
              dyadicScale e := by
            apply Finset.sum_le_sum; intro c _; exact hbase i c
      _ = ((Finset.univ.filter (fun c : Fin (grayTailBranch q L a e) =>
        c.val < 2 ^ (e - a))).card : Rat) *
              dyadicScale e := by rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
            apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
            exact_mod_cast grayTail_source_fin_card_le (grayTailBranch q L a e) (2 ^ (e - a))
  calc
    (∑ i : Fin n, ∑ c : Fin (grayTailBranch q L a e),
        if c.val < 2 ^ (e - a) then
          grayTailFrozenSonBase _ i c else 0) <=
        ∑ _i : Fin n, ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
          apply Finset.sum_le_sum; intro i _; exact hinner i
    _ = ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast; ring

/-- **The V2 frozen-tail request sum lower bound.**  Each tail round supplies
the call-depth-scale request (heart), so the tail sum is at least
`tail.length · (n·source/4)·(3/4)·dyadicScale(callDepth)`. -/
theorem grayChargedBlockV2_frozenTailRequestSum_lower {n q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {t : Nat} :
    (((frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t)).tail.length : Nat) : Rat) *
        (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) <=
      halfAmplification q * grayTailFrozenRequestSum
        (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t)).tail := by
  apply grayTailFrozenRequestSum_lower_of_each
  intro p hp
  have htm : (frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t)).tail =
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen.tail.map GrayTailRoundV2.toV1 := by
    rw [frozenV1OfV2]
    rcases (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).frozen with _ | ⟨hd0, tl0⟩ <;> simp
  rw [htm, List.mem_map] at hp
  obtain ⟨q0, hq0, rfl⟩ := hp
  have hcert := grayChargedBlockTailCertifiedV2_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hrv := hcert.round_valid q0 (List.mem_of_mem_tail hq0)
  have hwidth := (grayBlockWidthInvariantV2_stateAt (n := n) q L a e sigma A sm t).frozenTail
    q0 hq0
  have hheart := grayChargedBlockV2_perRound_request_lower
    (n := n) (b' := grayTailBranch q L a e) (q := q) (L := L) (a := a) (e := e)
    (A' := q0.unavailable) (slots := q0.slots) (move := q0.move)
    (server := grayTailLocalServerMove q0.fineEnd q0.slots (sm q0.serverTime))
    (r := q0.roundIndex)
    hrv.2.2.2.2.2.2.1
    (by
      have := hwidth
      simpa [grayChargedSourceCount] using this)
  have hsc : ((n * grayChargedSourceCount a e : Nat) : Rat) =
      ((n * 2 ^ (e - a) : Nat) : Rat) := by
    rw [grayChargedSourceCount]
  simpa [GrayTailRoundV2.toV1, hsc] using hheart

/-- V2 block-goal root requests are nonnegative (per slot entry). -/
lemma grayChargedBlockSlotEntries_root_nonneg
    {n b q L e r : Nat} {A : Allocation}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : grayChargedBlockGoalAtB q L e r slots.length A move server = true) :
    forall z, z ∈ grayTailSlotEntries slots move -> 0 <= getReq z.2 [] := by
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  have hj := (grayChargedBlockGoalAtB_root_bounds hgoal j).1
  unfold getFamilyReq at hj
  have hscale : 0 <= dyadicScale (grayTailRoundEps q L e r) / 2 :=
    div_nonneg (dyadicScale_pos _).le (by norm_num)
  exact le_trans hscale hj

/-- **V2 terminal progress: reaching the advantage round count empties the
active slots.**  Mirror of the V1 endgame, on the strict `GrayTailRoundV2`
controller via `frozenV1OfV2`. -/
theorem grayChargedBlockTail_slots_eq_nil_of_roundCount_stateAt_global
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hcount : grayChargedAdvantageRoundCount q <=
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen.length) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
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
  -- the V1-projected frozen list
  set F := frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t) with hF
  have hFlen : F.length =
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen.length := by
    rw [hF, frozenV1OfV2, List.length_map]
  have hroundNonneg : forall p, p ∈ F ->
      0 <= totalRootRequest p.slots.length p.move := by
    intro p hp
    rw [hF, frozenV1OfV2, List.mem_map] at hp
    obtain ⟨q0, hq0, rfl⟩ := hp
    have hvalid := (grayChargedBlockTailCertifiedV2_stateAt
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t).round_valid q0 hq0
    have hgoal := hvalid.2.2.2.2.2.2.1
    rw [totalRootRequest_eq_grayTailEntryRequestSum]
    apply grayTailEntryRequestSum_nonneg
    have hnn := grayChargedBlockSlotEntries_root_nonneg (q := q) (L := L) (e := e)
      (r := q0.roundIndex) (A := q0.unavailable) (slots := q0.slots)
      (move := q0.move)
      (server := grayTailLocalServerMove q0.fineEnd q0.slots (sm q0.serverTime))
      hgoal
    intro z hz
    exact hnn z (by simpa [GrayTailRoundV2.toV1] using hz)
  have htailAll := grayTailFrozenRequestSum_tail_le F hroundNonneg
  have hupper := grayChargedBlockV2_frozenRequestSum_le_source_budget
    (n := n) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have htailUpper : grayTailFrozenRequestSum F.tail <=
      ((n * 2 ^ (e - a) : Nat) : Rat) * dyadicScale e :=
    le_trans htailAll (by rw [hF]; exact hupper)
  have hlower := grayChargedBlockV2_frozenTailRequestSum_lower
    (n := n) (q := q) (L := L) (a := a) (e := e)
    (sigma := sigma) (A := A) (sm := sm) (t := t)
  have hlower' : ((F.tail.length : Nat) : Rat) *
        (((n * 2 ^ (e - a) : Nat) : Rat) / 4 *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))) <=
      halfAmplification q * grayTailFrozenRequestSum F.tail := by
    rw [hF]; exact hlower
  have hkpos := halfAmplification_pos q
  have hlowerUpper := le_trans hlower'
    (mul_le_mul_of_nonneg_left htailUpper hkpos.le)
  have hroundPos : 1 <= grayChargedAdvantageRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq]
    have hq : 0 < (q + 1) ^ 2 := by positivity
    omega
  have htailCount : grayChargedAdvantageRoundCount q - 1 <= F.tail.length := by
    rw [List.length_tail, hFlen]
    omega
  have htailCountRat :
      ((grayChargedAdvantageRoundCount q - 1 : Nat) : Rat) <=
      ((F.tail.length : Nat) : Rat) := by
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

/-- **V2 step-level acceptance dichotomy** (mirror of the V1
`grayChargedTailStep_width_or_roundCount_of_done`, in the fibre-count-correct
narrow form): once the controller stops after a step, either the *narrow*
fibre quarter has fired or the advantage round count has been reached.  The
quarter is on `grayTailNextSlots` (distinct active fibres), not on the wide
block, per the soundness fix. -/
lemma grayChargedBlockTailStepV2_narrowQuarter_or_roundCount_of_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A st sm).done = true) :
    GrayTailGlobalQuarter (n := n) (b := b) (grayChargedSourceCount a e)
        (grayTailNextSlots e (grayChargedSourceCount a e)
          (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
          A
          ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
            GrayTailRoundV2.toV1)
          sm)
      ∨ grayChargedAdvantageRoundCount q <=
        (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length := by
  by_cases hs : st.slots.isEmpty = true
  · exfalso
    simp only [grayChargedBlockTailStepV2, hactive, hs, Bool.false_eq_true,
      ↓reduceIte] at hdone
  · have hs' : st.slots.isEmpty = false := by simpa using hs
    by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
        st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true
    · simp only [grayChargedBlockTailStepV2, hactive, hs', hg,
        Bool.false_eq_true, ↓reduceIte] at hdone ⊢
      rw [Bool.or_eq_true] at hdone
      rcases hdone with h | h
      · exact Or.inl ((grayTailGlobalQuarterB_eq_true_iff _ _).mp h)
      · exact Or.inr (by simpa using h)
    · exfalso
      simp only [grayChargedBlockTailStepV2, hactive, hs', hg,
        Bool.false_eq_true, ↓reduceIte] at hdone

/-- **Accept-branch terminal slots equation.**  When a round is accepted, the
controller's new active slots are exactly the wide block `grayBlockNextSlots`
at the next round index, over the (V1-projected) extended frozen list.  A
structural fact used by the endgame source accounting. -/
lemma grayChargedBlockTailStepV2_accept_slots {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hactive : st.done = false) (hs : st.slots.isEmpty = false)
    (hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
        st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true) :
    (grayChargedBlockTailStepV2 q L a e sigma A st sm).slots =
      grayBlockNextSlots q L e (grayChargedSourceCount a e)
        (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
        ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
          GrayTailRoundV2.toV1) sm := by
  simp only [grayChargedBlockTailStepV2, hactive, hs, hg, Bool.false_eq_true,
    ↓reduceIte]

/-- The accept-branch terminal frozen list is the extended list. -/
lemma grayChargedBlockTailStepV2_accept_frozen {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hactive : st.done = false) (hs : st.slots.isEmpty = false)
    (hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
        st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true) :
    (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length =
      st.frozen.length + 1 := by
  simp only [grayChargedBlockTailStepV2, hactive, hs, hg, Bool.false_eq_true,
    ↓reduceIte, List.length_append, List.length_cons, List.length_nil]

/-- **V2 wide-block width dichotomy** (endgame-facing form).  Combining the
narrow fibre quarter with the wide/narrow length bridge, once the controller
stops the wide terminal block has at most `n·source·mult` slots — the
`mult`-scaled width of the round — or the advantage round count was reached. -/
lemma grayChargedBlockTailStepV2_wideWidth_or_roundCount_of_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A st sm).done = true)
    (hr : st.frozen.length + 1 < b) :
    4 * (grayChargedBlockTailStepV2 q L a e sigma A st sm).slots.length <=
        n * grayChargedSourceCount a e *
          (grayAdvBlockGrandsons b q L
            (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length).length
      ∨ grayChargedAdvantageRoundCount q <=
        (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length := by
  by_cases hs : st.slots.isEmpty = true
  · exfalso
    simp only [grayChargedBlockTailStepV2, hactive, hs, Bool.false_eq_true,
      ↓reduceIte] at hdone
  · have hs' : st.slots.isEmpty = false := by simpa using hs
    by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
        st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true
    · have hslots := grayChargedBlockTailStepV2_accept_slots q L a e sigma A st sm
        hactive hs' hg
      have hfroz := grayChargedBlockTailStepV2_accept_frozen q L a e sigma A st sm
        hactive hs' hg
      have hr' : (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length < b := by
        rw [hfroz]; exact hr
      rcases grayChargedBlockTailStepV2_narrowQuarter_or_roundCount_of_done
        q L a e sigma A st sm hactive hdone with hq | hrc
      · left
        rw [hslots, grayBlockNextSlots_length q L e (grayChargedSourceCount a e)
          ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length)
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
          ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
            GrayTailRoundV2.toV1) sm hr']
        have hnarrow : 4 * (grayTailNextSlots e (grayChargedSourceCount a e)
            ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length)
            (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
            ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
              GrayTailRoundV2.toV1) sm).length <=
              n * grayChargedSourceCount a e := hq
        calc 4 * ((grayTailNextSlots e (grayChargedSourceCount a e)
                ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length)
                (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
                ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
                  GrayTailRoundV2.toV1) sm).length *
              (grayAdvBlockGrandsons b q L
                (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length).length)
            = (4 * (grayTailNextSlots e (grayChargedSourceCount a e)
                ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length)
                (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
                ((grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.map
                  GrayTailRoundV2.toV1) sm).length) *
              (grayAdvBlockGrandsons b q L
                (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length).length := by
                ring
          _ <= (n * grayChargedSourceCount a e) *
              (grayAdvBlockGrandsons b q L
                (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length).length :=
                Nat.mul_le_mul hnarrow le_rfl
          _ = n * grayChargedSourceCount a e *
              (grayAdvBlockGrandsons b q L
                (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length).length := by
                ring
      · exact Or.inr hrc
    · exfalso
      simp only [grayChargedBlockTailStepV2, hactive, hs', hg,
        Bool.false_eq_true, ↓reduceIte] at hdone

/-- The V2 step preserves a set `done` flag. -/
lemma grayChargedBlockTailStepV2_done_stable {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (h : st.done = true) :
    (grayChargedBlockTailStepV2 q L a e sigma A st sm).done = true := by
  simp only [grayChargedBlockTailStepV2, h, if_true]

/-- The V2 step never shrinks the frozen list. -/
lemma grayChargedBlockTailStepV2_frozen_length_le {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove) :
    st.frozen.length <=
      (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen.length := by
  by_cases hd : st.done = true
  · exact le_of_eq (by simp [grayChargedBlockTailStepV2, hd])
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · exact le_of_eq (by simp [grayChargedBlockTailStepV2, hd', hs])
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
          st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · rw [grayChargedBlockTailStepV2_accept_frozen q L a e sigma A st sm
          hd' hs' hg]
        omega
      · exact le_of_eq (by simp [grayChargedBlockTailStepV2, hd', hs', hg])

/-- Frozen length is monotone along the V2 state trajectory. -/
lemma grayChargedBlockTailStateAtV2_frozen_length_le {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t).frozen.length <=
      (grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm (t + 1)).frozen.length := by
  rw [grayChargedBlockTailStateAtV2_succ]
  exact grayChargedBlockTailStepV2_frozen_length_le q L a e sigma A _ (sm t)

/-- The V2 `done` flag, once set, stays set at the next time. -/
lemma grayChargedBlockTailStateAtV2_done_stable_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (h : (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t).done = true) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm (t + 1)).done = true := by
  rw [grayChargedBlockTailStateAtV2_succ]
  exact grayChargedBlockTailStepV2_done_stable q L a e sigma A _ (sm t) h

/-- The V2 `done` flag is monotone in time. -/
lemma grayChargedBlockTailStateAtV2_done_mono {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) {t t' : Nat} (htt : t <= t')
    (h : (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t).done = true) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t').done = true := by
  induction t', htt using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
      exact grayChargedBlockTailStateAtV2_done_stable_succ q L a e sigma A sm m ih

/-- Every frozen V2 round was recorded strictly before the current time. -/
lemma grayChargedBlockTailStateAtV2_frozen_serverTime_lt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (p : GrayTailRoundV2 n b)
    (hp : p ∈ (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t).frozen) :
    p.serverTime < t :=
  ((grayChargedBlockTailCertifiedV2_stateAt (n := n) (b := b)
    q L a e sigma A sm t).round_valid p hp).2.2.2.2.1

/-- The V2 frozen list never exceeds the advantage round count. -/
lemma grayChargedBlockTailStateAtV2_frozen_length_le_roundCount {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t).frozen.length <= grayChargedAdvantageRoundCount q :=
  ((grayChargedBlockTailCertifiedV2_stateAt (n := n) (b := b)
    q L a e sigma A sm t).frozen_bound).1

/-- The V2 shape invariant holds at every trajectory point. -/
lemma grayBlockTailShapeV2_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayBlockTailShapeV2 q L
      (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t) :=
  (grayChargedBlockTailCertifiedV2_stateAt (n := n) (b := b)
    q L a e sigma A sm t).shape

/-- The accept-branch frozen list is the old list with the accepted round
appended (explicit record form). -/
lemma grayChargedBlockTailStepV2_accept_frozen_eq {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hactive : st.done = false) (hs : st.slots.isEmpty = false)
    (hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
        st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm) = true) :
    (grayChargedBlockTailStepV2 q L a e sigma A st sm).frozen =
      st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           blockAnchor := grayTailRoundEps q L e st.frozen.length
           childEps := grayTailRoundEps q L e st.frozen.length +
             graySpendSpan q
           fineEnd := grayTailRoundDelta q L e st.frozen.length
           slots := st.slots
           move := grayBlockCurrentMoveV2 q L e sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayTailRoundDelta q L e st.frozen.length) st.slots sm)
           unavailable := st.unavailable }] := by
  simp only [grayChargedBlockTailStepV2, hactive, hs, hg, Bool.false_eq_true,
    ↓reduceIte]

end Kolmogorov
