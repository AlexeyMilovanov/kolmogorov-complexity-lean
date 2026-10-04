import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOuterSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChildBranching
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Spec
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# Reachability support of the V2 charged outer strategy

Port of `GacsDayChargedOuterSupport` (the V1 fields
`grayChargedStrategy_rangeSupported` / `grayChargedStrategy_treeSupported`) to
the V2 block controller `grayChargedStrategyV2`.

Every sub-move the V2 controller ever displays — frozen or current, in the
advantage or in the spend phase — is a move of the pinned child rung
`PinnedChargedRung 4 q sigma` at some anchor `a' ≥ 1` with child ε
`a' + graySpendSpan q`.  The rung's game specification gives range support on
the child ladder branching, which the outer `grayTailBranch q L a e` dominates
(`grayChildBranching_le_baseBranch`), and tree support at height `2 * q`.  The
invariant "every frozen round stores a supported move" is carried along
`grayChargedFoldV2`, and the two-level graft turns the entry support into
`FamilyRangeSupported` / `FamilyTreeSupported` of the outer strategy.
-/

namespace Kolmogorov

/-! ### Support of the pinned rung's sub-moves on the outer tree -/

/-- A sub-move of the pinned rung at anchor `a' ≥ 1` (child ε at
`a' + graySpendSpan q`) is range supported on the outer tree and tree
supported at height `2 * q`, as soon as the parent's per-round budget
dominates the child's footprint. -/
lemma grayChargedV2_pinnedMove_supported
    {q L a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    {a' : ℕ} (ha' : 1 ≤ a') {n' : ℕ} (hn' : 1 ≤ n') (hist : FamilyGameHistory)
    {j : ℕ} (hj : j < n') :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt (sigma a' (a' + graySpendSpan q) A' n' hist) j) := by
  have hbase := hRung a' ha' n' A' hn'
  have hspan : a' + 8 * grayFootprint (q - 1) + 3 = a' + graySpendSpan q := by
    unfold graySpendSpan
    omega
  have hbranch :
      ladderBranching (grayTailBaseBranch (q - 1) (grayFootprint (q - 1))) a'
          (a' + 8 * grayFootprint (q - 1) + 3) ≤ grayTailBranch q L a e := by
    rw [hspan]
    exact le_trans (grayChildBranching_le_baseBranch hL) (le_max_right _ _)
  have hspec := (hbase.mono_branching hbranch).weak
  rw [hspan] at hspec
  constructor
  · intro y k hk
    exact hspec.range_supported hist y k hk j hj
  · intro y hy
    exact hspec.tree_supported hist y hy j hj

/-- The advantage sub-move at the block anchor `grayTailRoundEps q L e r` is
supported (the anchor is positive since `grayCallDepth q e ≥ 2`). -/
lemma grayChargedV2_rungMove_supported
    {q L a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (r n' : ℕ) (hn' : 1 ≤ n') (hist : FamilyGameHistory) {j : ℕ} (hj : j < n') :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt
        (sigma (grayTailRoundEps q L e r)
          (grayTailRoundEps q L e r + graySpendSpan q) A' n' hist) j) := by
  have hcall : 1 ≤ grayCallDepth q e := by
    unfold grayCallDepth
    omega
  exact grayChargedV2_pinnedMove_supported hL hRung
    (le_trans hcall (grayTailRoundEps_lower q L e r)) hn' hist hj

/-- The spend sub-move at the pass anchor `grayChargedSpendEps a L e pass` is
supported (the anchor is at least `a + 3`). -/
lemma grayChargedV2_spendMove_supported
    {q L a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (pass n' : ℕ) (hn' : 1 ≤ n') (hist : FamilyGameHistory) {j : ℕ} (hj : j < n') :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt
        (sigma (grayChargedSpendEps a L e pass)
          (grayChargedSpendEps a L e pass + graySpendSpan q) A' n' hist) j) := by
  have hEps : 1 ≤ grayChargedSpendEps a L e pass := by
    unfold grayChargedSpendEps grayChargedSpendAlphaDepth
    omega
  exact grayChargedV2_pinnedMove_supported hL hRung hEps hn' hist hj

/-- The current advantage sub-move of a V2 core with nonempty slots is
supported at every active slot. -/
lemma grayBlockCurrentMoveV2_supported
    {q L a e n b : ℕ} {sigma : FamilyStrategyScheme}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n b) (hne : 1 ≤ st.slots.length)
    {j : ℕ} (hj : j < st.slots.length) :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma st) j) :=
  grayChargedV2_rungMove_supported hL hRung st.frozen.length st.slots.length hne
    st.history hj

/-- The current spend sub-move of a V2 core with nonempty slots is supported
at every active slot. -/
lemma grayBlockSpendMoveV2_supported
    {q L a e n b pass : ℕ} {sigma : FamilyStrategyScheme}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n b) (hne : 1 ≤ st.slots.length)
    {j : ℕ} (hj : j < st.slots.length) :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt (grayBlockSpendMoveV2 q L a e pass sigma st) j) :=
  grayChargedV2_spendMove_supported hL hRung pass st.slots.length hne st.history hj

/-! ### The frozen-entries-supported invariant of the V2 fold -/

/-- Every frozen V2 round stores a recursive move that is range supported on
the tree of branching `b` and tree supported at height `2 * q`. -/
def GrayChargedFrozenSupportedV2 {n b : ℕ} (q : ℕ)
    (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    GrayChargedEntryMoveSupported q b (familyClientMoveAt p.move j)

/-- An empty list of V2 frozen rounds is supported. -/
lemma grayChargedFrozenSupportedV2_nil {n b : ℕ} (q : ℕ) :
    GrayChargedFrozenSupportedV2 q ([] : List (GrayTailRoundV2 n b)) := by
  intro p hp
  simp at hp

/-- Freezing a round whose move is supported keeps the V2 frozen rounds supported. -/
lemma grayChargedFrozenSupportedV2_append {n b q : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenSupportedV2 q frozen) (p : GrayTailRoundV2 n b)
    (hp : ∀ j < p.slots.length,
      GrayChargedEntryMoveSupported q b (familyClientMoveAt p.move j)) :
    GrayChargedFrozenSupportedV2 q (frozen ++ [p]) := by
  intro p' hp' j hj
  rcases List.mem_append.mp hp' with h | h
  · exact hst p' h j hj
  · rw [List.mem_singleton] at h
    subst h
    exact hp j hj

/-- The V1 projection of the ledger inherits the invariant (`toV1` keeps the
slots and the move). -/
lemma grayChargedFrozenSupportedV2_toV1 {n b q : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenSupportedV2 q frozen) :
    GrayChargedFrozenSupported q (frozen.map GrayTailRoundV2.toV1) := by
  intro p hp j hj
  rw [List.mem_map] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact hst p' hp' j hj

/-- The strict V2 advantage step preserves the invariant: an accepted round
freezes the current advantage sub-move, which the pinned rung supports. -/
lemma grayChargedBlockTailStepV2_frozen_supported
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e)) (m : FamilyServerMove)
    (hst : GrayChargedFrozenSupportedV2 q st.frozen) :
    GrayChargedFrozenSupportedV2 q
      (grayChargedBlockTailStepV2 q L a e sigma A st m).frozen := by
  by_cases hd : st.done = true
  · simpa [grayChargedBlockTailStepV2, hd] using hst
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedBlockTailStepV2, hd', hs] using hst
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots m) = true
      · have hne : 1 ≤ st.slots.length := by
          cases hsl : st.slots with
          | nil => simp [hsl] at hs'
          | cons _ _ => simp
        rw [grayChargedBlockTailStepV2_accept_frozen_eq q L a e sigma A st m hd' hs' hg]
        exact grayChargedFrozenSupportedV2_append hst _
          (fun j hj => grayBlockCurrentMoveV2_supported hL hRung st hne hj)
      · simpa [grayChargedBlockTailStepV2, hd', hs', hg] using hst

/-- The full V2 charged step preserves the invariant: the advantage phase
defers to the strict tail step (the spend start keeps the ledger), and an
accepted spend pass freezes the current spend sub-move. -/
lemma grayChargedFrozenSupportedV2_step
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayChargedStateV2 n (grayTailBranch q L a e)) (m : FamilyServerMove)
    (hst : GrayChargedFrozenSupportedV2 q st.core.frozen) :
    GrayChargedFrozenSupportedV2 q
      (grayChargedStepV2 q L a e sigma A st m).core.frozen := by
  cases hphase : st.phase with
  | done => simpa [grayChargedStepV2, hphase] using hst
  | advantage =>
      have hnext := grayChargedBlockTailStepV2_frozen_supported (A := A)
        hL hRung st.core m hst
      simp only [grayChargedStepV2, hphase]
      by_cases hdone :
          (grayChargedBlockTailStepV2 q L a e sigma A st.core m).done = true
      · rw [ite_eq_left hdone]
        by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A st.core m) m = true
        · rw [ite_eq_left hserved, grayChargedStartSpendV2_frozen]
          exact hnext
        · rw [ite_eq_right hserved]
          exact hnext
      · simpa [hdone] using hnext
  | spend pass =>
      by_cases hslots : st.core.slots.isEmpty = true
      · simpa [grayChargedStepV2, hphase, hslots] using hst
      · have hslots' : st.core.slots.isEmpty = false := by simpa using hslots
        have hne : 1 ≤ st.core.slots.length := by
          cases hsl : st.core.slots with
          | nil => simp [hsl] at hslots'
          | cons _ _ => simp
        by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable
            (grayBlockSpendMoveV2 q L a e pass sigma st.core)
            (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              st.core.slots m) = true
        · have hcur : ∀ j < st.core.slots.length,
              GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
                (familyClientMoveAt
                  (grayBlockSpendMoveV2 q L a e pass sigma st.core) j) :=
            fun j hj => grayBlockSpendMoveV2_supported hL hRung st.core hne hj
          simp only [grayChargedStepV2, hphase, hslots', Bool.false_eq_true,
            ↓reduceIte, hgoal]
          split
          · split
            · exact grayChargedFrozenSupportedV2_append hst _ hcur
            · exact grayChargedFrozenSupportedV2_append hst _ hcur
          · exact grayChargedFrozenSupportedV2_append hst _ hcur
        · simpa [grayChargedStepV2, hphase, hslots', hgoal] using hst

/-- **The invariant along the V2 fold**: every frozen round of the fold state
stores a supported recursive move. -/
lemma grayChargedFoldV2_frozen_supported
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (history : List FamilyServerMove) :
    GrayChargedFrozenSupportedV2 q
      (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
        history).core.frozen := by
  have key : ∀ (hist : List FamilyServerMove)
      (st : GrayChargedStateV2 n (grayTailBranch q L a e)),
      GrayChargedFrozenSupportedV2 q st.core.frozen →
      GrayChargedFrozenSupportedV2 q
        (hist.foldl (grayChargedStepV2 q L a e sigma A) st).core.frozen := by
    intro hist
    induction hist with
    | nil =>
        intro st hst
        simpa using hst
    | cons m rest ih =>
        intro st hst
        rw [List.foldl_cons]
        exact ih _ (grayChargedFrozenSupportedV2_step hL hRung st m hst)
  have h0 : GrayChargedFrozenSupportedV2 q
      (grayChargedInitialStateV2 n (grayTailBranch q L a e) a e q L A).core.frozen :=
    grayChargedFrozenSupportedV2_nil q
  exact key history _ h0

/-! ### The displayed move and its entries -/

/-- The current sub-move displayed by the V2 charged controller in one state:
the advantage or spend sub-move on nonempty slots, `[]` otherwise. -/
def grayChargedCurrentMoveV2 {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayChargedStateV2 n b) : FamilyClientMove :=
  match st.phase with
  | .done => []
  | .advantage => if st.core.done || st.core.slots.isEmpty then []
      else grayBlockCurrentMoveV2 q L e sigma st.core
  | .spend pass => if st.core.slots.isEmpty then []
      else grayBlockSpendMoveV2 q L a e pass sigma st.core

/-- The V2 charged strategy displays the graft of the projected ledger, the
active slots (none on a done core: the raised-service wait) and the current
sub-move of the fold state. -/
lemma grayChargedStrategyV2_eq_display
    (q L a e n : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (hist : FamilyGameHistory) :
    grayChargedStrategyV2 q L a e sigma A n hist =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
          hist.2).core.frozen.map GrayTailRoundV2.toV1)
        (if (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
          hist.2).core.done then []
        else (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
          hist.2).core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma
          (grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
            hist.2)) := by
  unfold grayChargedStrategyV2 grayChargedCurrentMoveV2
  generalize grayChargedFoldV2 (n := n) (b := grayTailBranch q L a e) q L a e sigma A
    hist.2 = st
  obtain ⟨phase, core⟩ := st
  cases phase <;> rfl

/-- The current sub-move of a V2 charged state is supported at every active
slot. -/
lemma grayChargedCurrentMoveV2_supported
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayChargedStateV2 n (grayTailBranch q L a e)) :
    ∀ j < st.core.slots.length,
      GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
        (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st) j) := by
  intro j hj
  have hne : 1 ≤ st.core.slots.length := by omega
  unfold grayChargedCurrentMoveV2
  cases st.phase with
  | advantage =>
      by_cases hcond : (st.core.done || st.core.slots.isEmpty) = true
      · rw [ite_eq_left hcond]
        exact grayChargedEntryMoveSupported_nil q _
      · rw [ite_eq_right hcond]
        exact grayBlockCurrentMoveV2_supported hL hRung st.core hne hj
  | spend pass =>
      by_cases hempty : st.core.slots.isEmpty = true
      · simp only [hempty]
        exact grayChargedEntryMoveSupported_nil q _
      · simp only [hempty]
        exact grayBlockSpendMoveV2_supported hL hRung st.core hne hj
  | done => exact grayChargedEntryMoveSupported_nil q _

/-- The current sub-move is supported at every displayed slot (none on a done
core). -/
lemma grayChargedCurrentMoveV2_supported_display
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme}
    (hL : grayFootprint (q - 1) ≤ L) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayChargedStateV2 n (grayTailBranch q L a e)) :
    ∀ j < (if st.core.done then [] else st.core.slots).length,
      GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
        (familyClientMoveAt (grayChargedCurrentMoveV2 q L a e sigma st) j) := by
  intro j hj
  by_cases hd : st.core.done = true
  · rw [ite_eq_left hd] at hj
    simp at hj
  · rw [ite_eq_right hd] at hj
    exact grayChargedCurrentMoveV2_supported hL hRung st j hj

/-- All entries of a projected ledger with a supported current move are
supported. -/
lemma grayChargedV2_entries_all_supported {n b q : ℕ}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hfrozen : GrayChargedFrozenSupported q frozen)
    (hcur : ∀ j < slots.length,
      GrayChargedEntryMoveSupported q b (familyClientMoveAt current j)) :
    ∀ pr ∈ grayTailEntries frozen slots current,
      GrayChargedEntryMoveSupported q b pr.2 := by
  intro pr hpr
  unfold grayTailEntries at hpr
  rw [List.mem_append] at hpr
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

/-- Range support of the two-level graft from the support of its entries. -/
lemma grayChargedTailFamilyMove_range_eq_zero {n b q : ℕ}
    {source : ℕ} {threshold eps : ℚ} {frozen : GrayTailFrozen n b}
    {slots : List (GrayTailSlot n b)} {current : FamilyClientMove}
    (hall : ∀ pr ∈ grayTailEntries frozen slots current,
      GrayChargedEntryMoveSupported q b pr.2)
    (x : GacsDayNode) {i : ℕ} (hi : b ≤ i) {j : ℕ} (hj : j < n) :
    getReq (familyClientMoveAt
      (grayChargedTailFamilyMove source threshold eps frozen slots current) j)
      (x ++ [i]) = 0 := by
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left hj]
  refine getReq_graftTwoLevel_eq_zero_of_range ?_ x hi
  intro c hc c' hc' y k hk
  simp only [hc, hc', dite_eq_left]
  exact (grayCharged_entryMove_supported hall _).1 y k hk

/-- Tree support of the two-level graft from the support of its entries. -/
lemma grayChargedTailFamilyMove_length_eq_zero {n b q : ℕ}
    {source : ℕ} {threshold eps : ℚ} {frozen : GrayTailFrozen n b}
    {slots : List (GrayTailSlot n b)} {current : FamilyClientMove}
    (hall : ∀ pr ∈ grayTailEntries frozen slots current,
      GrayChargedEntryMoveSupported q b pr.2)
    (x : GacsDayNode) (hx : 2 * (q + 1) < x.length) {j : ℕ} (hj : j < n) :
    getReq (familyClientMoveAt
      (grayChargedTailFamilyMove source threshold eps frozen slots current) j)
      x = 0 := by
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left hj]
  refine getReq_graftTwoLevel_eq_zero_of_length (h := 2 * q) ?_ x (by omega)
  intro c hc c' hc' y hy
  simp only [hc, hc', dite_eq_left]
  exact (grayCharged_entryMove_supported hall _).2 y hy

/-! ### The outer support fields of the V2 charged strategy -/

/-- **Range support of the V2 charged outer strategy**: no request is ever
placed at a son of index `grayTailBranch q L a e` or more. -/
theorem grayChargedStrategyV2_rangeSupported
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma) :
    FamilyRangeSupported n (grayTailBranch q L a e) A
      (grayChargedStrategyV2 q L a e sigma) := by
  have hL' : grayFootprint (q - 1) ≤ L := by
    rw [hL]
    exact grayFootprint_pred_le q
  intro hist x i hi j hj
  rw [grayChargedStrategyV2_eq_display]
  exact grayChargedTailFamilyMove_range_eq_zero
    (grayChargedV2_entries_all_supported
      (grayChargedFrozenSupportedV2_toV1
        (grayChargedFoldV2_frozen_supported (A := A) hL' hRung hist.2))
      (grayChargedCurrentMoveV2_supported_display hL' hRung _)) x hi hj

/-- **Tree support of the V2 charged outer strategy**: no request is ever
placed below height `2 * (q + 1)`. -/
theorem grayChargedStrategyV2_treeSupported
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma) :
    FamilyTreeSupported n (2 * (q + 1)) A (grayChargedStrategyV2 q L a e sigma) := by
  have hL' : grayFootprint (q - 1) ≤ L := by
    rw [hL]
    exact grayFootprint_pred_le q
  intro hist x hx j hj
  rw [grayChargedStrategyV2_eq_display]
  exact grayChargedTailFamilyMove_length_eq_zero
    (grayChargedV2_entries_all_supported
      (grayChargedFrozenSupportedV2_toV1
        (grayChargedFoldV2_frozen_supported (A := A) hL' hRung hist.2))
      (grayChargedCurrentMoveV2_supported_display hL' hRung _)) x hx hj

end Kolmogorov
