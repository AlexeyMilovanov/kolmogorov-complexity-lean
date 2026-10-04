import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFibre
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafD

/-!
# Gacs-Day ladder tail: entry support

The standing data of a gray-tail run and the support of its entries.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ### The standing data of a gray-tail run -/

/-- The gray-tail controller state after the first `t` server moves of `sm`, on the branch
`grayTailBranch q L a e`.  This is `grayTailStateAt` with its branch argument fixed to the
tail branch, the only instance the tail arguments make sense for. -/
abbrev grayTailBranchStateAt (n q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ) : GrayTailState n (grayTailBranch q L a e) :=
  grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t

/-- The standing hypotheses under which a gray-tail run is analysed: the exponent window
`1 ≤ a ≤ e`, a rung budget `B` inside the robust range `max 2 (256 * (q + 1) * 2 ^ L)` for
which `sigma` is a robust rung, and a legal server play `sm` against the allocation `A` on
the branch `grayTailBranch q L a e`.  These five facts always travel together, and each of
them is used by every lemma that takes this bundle. -/
structure GrayTailRunLegal (n q L a e B : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) : Prop where
  /-- The tail exponent is positive. -/
  alpha_pos : 1 ≤ a
  /-- The tail exponent does not exceed the call exponent. -/
  alpha_le : a ≤ e
  /-- The rung budget lies in the robust range. -/
  budget_le : B ≤ max 2 (256 * (q + 1) * 2 ^ L)
  /-- `sigma` is a robust rung strategy for the budget `B`. -/
  rung : RobustGrayRung q L B sigma
  /-- The server play is legal for the allocation `A` on the tail branch. -/
  server_legal : familyServerPlayLegal n (grayTailBranch q L a e) A sm

/-! ### The displayed move as an explicit two-level graft -/

/-- The entry table `grayTailEntries st.frozen st.slots m` used by `grayTailOutput`, where `m` is
the empty list once `st.done` holds and `grayTailCurrentMove q L e sigma st` otherwise. -/
def grayTailOutputEntries {n b : ℕ} (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : List (GrayTailSlot n b × ClientMove) :=
  grayTailEntries st.frozen st.slots
    (if st.done then [] else grayTailCurrentMove q L e sigma st)

/-- The displayed move of one tree is literally the two-level graft of the
recursive moves stored in the entry table. -/
lemma familyClientMoveAt_grayTailOutput
    {n b q L a e i : ℕ} {sigma : FamilyStrategyScheme}
    (st : GrayTailState n b) (hi : i < n) :
    familyClientMoveAt (grayTailOutput q L a e sigma st) i =
      graftTwoLevel
        (grayTailRootRequest st.done (grayTailTargetFloor q a)
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
          (dyadicScale e) (grayTailOutputEntries q L e sigma st) ⟨i, hi⟩)
        b
        (fun c =>
          if hc : c < b then
            grayTailSonRequest
              (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
              (dyadicScale e) (grayTailOutputEntries q L e sigma st) ⟨i, hi⟩ ⟨c, hc⟩
          else 0)
        (fun c c' =>
          if hc : c < b then
            if hc' : c' < b then
              grayTailEntryMove (grayTailOutputEntries q L e sigma st)
                (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩)
            else []
          else []) := by
  unfold grayTailOutput grayTailFamilyMove familyClientMoveAt grayTailOutputEntries
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-! ### E5a-E5b: support of the grafted recursive moves -/

/-- The support certificate carried by every recursive move grafted below an
outer grandson: it requests nothing at a son index `b` or beyond, and nothing
strictly below height `2 * q`. -/
def GrayTailEntryMoveSupported (q b : ℕ) (m : ClientMove) : Prop :=
  (∀ (y : GacsDayNode) (j : ℕ), b ≤ j → getReq m (y ++ [j]) = 0) ∧
  (∀ y : GacsDayNode, 2 * q < y.length → getReq m y = 0)

/-- The empty client move is supported. -/
lemma grayTailEntryMoveSupported_nil (q b : ℕ) :
    GrayTailEntryMoveSupported q b [] := by
  constructor <;> intro _ _ <;> simp [getReq]

/-- **Child E5a (proved).**  A lookup in a table of supported moves is
supported: either it finds a stored move, or it returns the empty move. -/
theorem grayTail_entryMove_supported {n b : ℕ} {q : ℕ}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, GrayTailEntryMoveSupported q b pr.2)
    (slot : GrayTailSlot n b) :
    GrayTailEntryMoveSupported q b (grayTailEntryMove entries slot) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none => simpa using grayTailEntryMoveSupported_nil q b
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hall pr hmem

/-- The moves returned by the preceding rung are supported. -/
lemma grayTail_rungMove_supported
    {q L B a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (r n' : ℕ) (hn' : 1 ≤ n') (hist : FamilyGameHistory)
    {j : ℕ} (hj : j < n') :
    GrayTailEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt
        (sigma (grayCallDepth q e) (grayTailRoundEps q L e r) A' n' hist) j) := by
  have hspec :=
    (hRung (grayCallDepth q e) (grayTailRoundEps q L e r)
      (le_trans (Nat.one_le_iff_ne_zero.mpr (by
        simp [grayCallDepth])) (le_refl _))
      (grayTailRoundEps_lower q L e r) n' A' hn').weak
  have hbranch :
      ladderBranching B (grayCallDepth q e) (grayTailRoundEps q L e r) ≤
        grayTailBranch q L a e :=
    le_trans (grayTailRecursiveBranch_le hB) (le_max_right _ _)
  constructor
  · intro y k hk
    exact hspec.range_supported hist y k (le_trans hbranch hk) j hj
  · intro y hy
    exact hspec.tree_supported hist y hy j hj

/-- Every stored entry of a state whose frozen moves are supported is
supported. -/
lemma grayTailEntries_all_supported {n b q : ℕ}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hfrozen : ∀ p ∈ frozen, ∀ j < p.slots.length,
      GrayTailEntryMoveSupported q b (familyClientMoveAt p.move j))
    (hcur : ∀ j < slots.length,
      GrayTailEntryMoveSupported q b (familyClientMoveAt current j)) :
    ∀ pr ∈ grayTailEntries frozen slots current,
      GrayTailEntryMoveSupported q b pr.2 := by
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

/-- The invariant carried through the controller fold: every frozen round
stores a supported recursive move. -/
def GrayTailFrozenSupported {n b : ℕ} (q : ℕ) (frozen : GrayTailFrozen n b) :
    Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    GrayTailEntryMoveSupported q b (familyClientMoveAt p.move j)

/-- A tail step keeps the frozen rounds supported. -/
lemma grayTailFrozenSupported_step
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e)) (sm : FamilyServerMove)
    (hst : GrayTailFrozenSupported q st.frozen) :
    GrayTailFrozenSupported q (grayTailStep q L a e sigma A st sm).frozen := by
  rw [grayTailStep_eq]
  by_cases hdone : st.done || st.slots.isEmpty
  · simpa [hdone] using hst
  · simp only [hdone, Bool.false_eq_true, ite_false]
    by_cases hgoal : familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length) st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots sm)
    · simp only [hgoal, ite_true]
      intro p hp j hj
      rcases List.mem_append.mp hp with hp | hp
      · exact hst p hp j hj
      · simp only [List.mem_singleton] at hp
        subst hp
        have hne : st.slots ≠ [] := by
          intro h
          simp [h] at hdone
        have hlen : 1 ≤ st.slots.length := List.length_pos_iff.mpr hne
        exact grayTail_rungMove_supported hB hRung st.frozen.length
          st.slots.length hlen st.history hj
    · simp only [hgoal]
      exact hst

/-- Replaying a whole history of server moves keeps the frozen rounds supported. -/
lemma grayTailFrozenSupported_fold
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (history : List FamilyServerMove)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hst : GrayTailFrozenSupported q st.frozen) :
    GrayTailFrozenSupported q
      (history.foldl (grayTailStep q L a e sigma A) st).frozen := by
  induction history generalizing st with
  | nil => simpa using hst
  | cons m history ih =>
      simp only [List.foldl_cons]
      exact ih _ (grayTailFrozenSupported_step hB hRung st m hst)

/-- **Child E5b (proved).**  Every recursive move grafted below a grandson of
the displayed tail move is supported. -/
theorem grayTail_fold_entries_supported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (history : List FamilyServerMove)
    (pr : GrayTailSlot n (grayTailBranch q L a e) × ClientMove)
    (hpr : pr ∈ grayTailOutputEntries q L e sigma
      (grayTailFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A
        history)) :
    GrayTailEntryMoveSupported q (grayTailBranch q L a e) pr.2 := by
  set st := grayTailFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A
    history with hstdef
  have hfrozen : GrayTailFrozenSupported q st.frozen := by
    rw [hstdef, grayTailFold]
    refine grayTailFrozenSupported_fold hB hRung history _ ?_
    intro p hp
    simp [grayTailInitialState] at hp
  refine grayTailEntries_all_supported hfrozen ?_ pr hpr
  intro j hj
  by_cases hdone : st.done
  · simp only [hdone, ite_true]
    have h_nil : [] = familyClientMoveAt [] j := rfl
    exact h_nil ▸ grayTailEntryMoveSupported_nil q (grayTailBranch q L a e)
  · simp only [hdone, Bool.false_eq_true, ite_false]
    have hlen : 1 ≤ st.slots.length := by omega
    exact grayTail_rungMove_supported hB hRung st.frozen.length
      st.slots.length hlen st.history hj

/-! ### E5c-E5d: the two support fields -/

/-- **Child E5c (proved).**  The tail controller never requests at a son index
beyond the outer branching. -/
theorem grayTailStrategy_rangeSupported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma) :
    FamilyRangeSupported n (grayTailBranch q L a e) A
      (grayTailStrategy q L a e sigma) := by
  intro hist x i hi j hj
  change getReq (familyClientMoveAt
    (grayTailOutput q L a e sigma
      (grayTailFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A
        hist.2)) j) (x ++ [i]) = 0
  rw [familyClientMoveAt_grayTailOutput _ hj]
  refine getReq_graftTwoLevel_eq_zero_of_range ?_ x hi
  intro c hc c' hc' y k hk
  simp only [hc, hc', dite_eq_left]
  exact (grayTail_entryMove_supported
    (fun pr hpr => grayTail_fold_entries_supported hB hRung hist.2 pr hpr) _).1 y k hk

/-- **Child E5d (proved).**  The tail controller never requests below height
`2 * (q + 1)`: the graft adds exactly two levels to the height `2 * q` of the
preceding rung. -/
theorem grayTailStrategy_treeSupported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma) :
    FamilyTreeSupported n (2 * (q + 1)) A (grayTailStrategy q L a e sigma) := by
  intro hist x hx j hj
  change getReq (familyClientMoveAt
    (grayTailOutput q L a e sigma
      (grayTailFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A
        hist.2)) j) x = 0
  rw [familyClientMoveAt_grayTailOutput _ hj]
  refine getReq_graftTwoLevel_eq_zero_of_length (h := 2 * q) ?_ x (by omega)
  intro c hc c' hc' y hy
  simp only [hc, hc', dite_eq_left]
  exact (grayTail_entryMove_supported
    (fun pr hpr => grayTail_fold_entries_supported hB hRung hist.2 pr hpr) _).2 y hy

/-! ### E5e-E5g: the three numerical outer fields -/

/-- The move assembled for a slot from nonnegative entries is nonnegative at every node. -/
lemma grayTailEntryMove_nonneg {n b : ℕ}
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
lemma grayTailEntryMove_child_le {n b : ℕ}
    (entries : List (GrayTailSlot n b × ClientMove))
    (hchild : ∀ p ∈ entries, ∀ x, getReq p.2 x ≥ ∑ c : Fin b, getReq p.2 (x ++ [c.val]))
    (slot : GrayTailSlot n b) (x : GacsDayNode) :
    getReq (grayTailEntryMove entries slot) x ≥
      ∑ c : Fin b, getReq (grayTailEntryMove entries slot) (x ++ [c.val]) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none => simp [getReq]
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hchild pr hmem x

/-- The root requests of the grandchildren below a son sum to at most that son's base. -/
lemma sum_grayTailEntryMove_root_le_grayTailSonBase {n b : ℕ}
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
      have hp_nonneg : 0 ≤ getReq m_p [] := hnonneg ((i_p, c1_p, c2_p), m_p) (by simp) []
      have hrest_nonneg : ∀ q ∈ rest, ∀ x, 0 ≤ getReq q.2 x :=
        fun q hq x => hnonneg q (by simp [hq]) x
      have hih := ih hrest_nonneg
      have hbase_def : grayTailSonBase rest i c = List.foldr (fun p acc =>
                                                               if p.1.1 = i ∧ p.1.2.1
        = c then getReq p.2 [] + acc else acc) 0 rest := rfl
      rw [hbase_def] at hih
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      by_cases hmatch : i_p = i ∧ c1_p = c
      · rw [ite_eq_left hmatch]
        have h_entry : ∀ c' : Fin b,
            grayTailEntryMove (((i_p, c1_p, c2_p), m_p) :: rest) (i, c, c') =
              if c2_p = c' then m_p else grayTailEntryMove rest (i, c, c') := by
          intro c'
          unfold grayTailEntryMove
          simp only [List.find?_cons]
          by_cases hc' : c2_p = c'
          · have hslot : (i_p, c1_p, c2_p) = (i, c, c') := by
              ext <;> simp [hmatch.1, hmatch.2, hc']
            rw [ite_eq_left hc']
            simp [hslot]
          · have hslot : (i_p, c1_p, c2_p) ≠ (i, c, c') := by
              intro h
              have : c2_p = c' := by injection h with _ h2; injection h2
              exact hc' this
            rw [ite_eq_right hc']
            simp [hslot]
        simp_rw [h_entry]
        have h_sum : (∑ c' : Fin b, getReq (if c2_p = c' then m_p else grayTailEntryMove rest (i,
                                                                                                c,
          c')) []) =
            getReq m_p [] + ∑ c' ∈ Finset.univ.erase c2_p, getReq (grayTailEntryMove rest (i, c,
                                                                                            c')) []
              := by
          have h_eq : (fun c' => getReq (if c2_p = c' then m_p else grayTailEntryMove rest (i,
                                                                                             c,
            c')) []) =
              (fun c' => if c2_p = c' then getReq m_p [] else getReq (grayTailEntryMove rest (i, c,
                                                                                               c'))
                []) := by
            funext c'
            split_ifs <;> rfl
          rw [h_eq, Finset.sum_ite]
          have hfilter : (Finset.univ.filter (fun c' : Fin b => c2_p = c')) = {c2_p} := by
            ext x; simp [eq_comm]
          have hfilter_ne : (Finset.univ.filter (fun c' : Fin b =>
                                                  ¬c2_p = c')) = Finset.univ.erase c2_p := by
            ext x; simp [ne_comm]
          rw [hfilter, hfilter_ne, Finset.sum_singleton]
        rw [h_sum]
        have h_sub : (∑ c' ∈ Finset.univ.erase c2_p, getReq (grayTailEntryMove rest (i,
                                                                                      c, c')) []) ≤
            ∑ c' : Fin b, getReq (grayTailEntryMove rest (i, c, c')) [] := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
          intro c' _ _
          exact grayTailEntryMove_nonneg rest hrest_nonneg (i, c, c') []
        linarith
      · rw [ite_eq_right hmatch]
        have h_entry : ∀ c' : Fin b,
            grayTailEntryMove (((i_p, c1_p, c2_p), m_p) :: rest) (i, c,
                                                                   c') = grayTailEntryMove rest (i,
                                                                                                  c,
              c') := by
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

/-- A tail run puts nothing on children outside the source range `2 ^ (e - a)`. -/
lemma grayTailSonBase_eq_zero_of_source_ge_stateAt
    {n q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) (hc : 2 ^ (e - a) ≤ c.val) :
    grayTailSonBase (grayTailOutputEntries q L e sigma (grayTailStateAt (n := n) (b :=
                                                                                   grayTailBranch q
      L a e) q L a e sigma A sm t)) i c = 0 := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  unfold grayTailOutputEntries grayTailEntries
  rw [grayTailSonBase_append_globalEntries]
  have hfrozen : grayTailSonBase (grayTailFrozenEntries st.frozen) i c = 0 := by
    change grayTailFrozenSonBase st.frozen i c = 0
    exact grayTail_frozen_sonBase_eq_zero_of_source_ge
      (q := q) (L := L) (a := a) (e := e) (t := t) (sigma := sigma) (A := A) (sm := sm) i c hc
  have hslots : grayTailSonBase (grayTailSlotEntries st.slots (if st.done then [] else
                                                                grayTailCurrentMove q L e sigma st))
    i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro p hp
    rw [grayTailSlotEntries, List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    right
    intro hmatch
    have hmem : st.slots.get j ∈ st.slots := List.get_mem _ _
    have hsource :=
      (grayTailSourceInvariant_stateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm
        t).current (st.slots.get j) hmem
    have hval : (st.slots.get j).2.1.val = c.val := congrArg Fin.val hmatch
    omega
  rw [hfrozen, hslots, add_zero]

/-- Every son request displayed by a tail run stays at most `dyadicScale e`. -/
lemma grayTailSonRequest_le_dyadicScale
    {n q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    grayTailSonRequest (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) (dyadicScale e)
      (grayTailOutputEntries q L e sigma (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L
                                           a e sigma A sm t)) i c ≤ dyadicScale e := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  set entries := grayTailOutputEntries q L e sigma st
  set thresh := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
  set eps := dyadicScale e
  unfold grayTailSonRequest
  dsimp
  split_ifs with h
  · exact le_rfl
  · have hthresh_le : thresh ≤ eps := by
      have hk := halfAmplification_pos q
      have heps := dyadicScale_pos e
      have : 0 ≤ dyadicScale e / (6 * halfAmplification q) := by positivity
      linarith
    exact le_trans (not_lt.mp h) hthresh_le

/-- A tail run requests nothing at children outside the source range `2 ^ (e - a)`. -/
lemma grayTailSonRequest_eq_zero_of_source_ge
    {n q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) (hc : 2 ^ (e - a) ≤ c.val) :
    grayTailSonRequest (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) (dyadicScale e)
      (grayTailOutputEntries q L e sigma (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L
                                           a e sigma A sm t)) i c = 0 := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  set entries := grayTailOutputEntries q L e sigma st
  set thresh := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
  set eps := dyadicScale e
  have hbase : grayTailSonBase entries i c = 0 :=
    grayTailSonBase_eq_zero_of_source_ge_stateAt (q := q) (L := L) (a := a) (e := e) (t :=
                                                                                       t) (sigma :=
                                                                                            sigma)
      (A := A) (sm := sm) i c hc
  unfold grayTailSonRequest
  dsimp
  rw [hbase]
  have hthresh_nonneg : 0 ≤ thresh := grayTail_threshold_nonneg_global q e
  rw [ite_eq_right (not_lt_of_ge hthresh_nonneg)]

/-- The son requests of a client displayed by a tail run sum to at most `dyadicScale a`. -/
lemma sum_grayTailSonRequest_le_dyadicScale
    {n q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hae : a ≤ e) (i : Fin n) :
    ∑ c : Fin (grayTailBranch q L a e),
      grayTailSonRequest (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) (dyadicScale e)
        (grayTailOutputEntries q L e sigma (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q
                                             L a e sigma A sm t)) i c ≤ dyadicScale a := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  set entries := grayTailOutputEntries q L e sigma st
  set thresh := dyadicScale e - dyadicScale e / (6 * halfAmplification q)
  set eps := dyadicScale e
  set used := 2 ^ (e - a)
  calc
    ∑ c : Fin (grayTailBranch q L a e), grayTailSonRequest thresh eps entries i c
      ≤ ∑ c : Fin (grayTailBranch q L a e), if c.val < used then eps else 0 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : c.val < used
        · rw [ite_eq_left hc]
          exact grayTailSonRequest_le_dyadicScale (q := q) (L := L) (a := a) (e := e) (t :=
                                                                                        t) (sigma :=
                                                                                             sigma)
            (A := A) (sm := sm) i c
        · rw [ite_eq_right hc]
          have hzero :=
            grayTailSonRequest_eq_zero_of_source_ge (q := q) (L := L) (a := a) (e := e) (t :=
                                                                                          t)
            (sigma := sigma) (A := A) (sm := sm) i c (by omega)
          rw [hzero]
    _ = ∑ c ∈ (Finset.univ.filter (fun c : Fin (grayTailBranch q L a e) => c.val < used)), eps := by
        rw [Finset.sum_filter]
    _ = ((Finset.univ.filter (fun c : Fin (grayTailBranch q L a e) =>
                               c.val < used)).card : ℚ) * eps := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (used : ℚ) * eps := by
        apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
        exact_mod_cast grayTail_source_fin_card_le (grayTailBranch q L a e) used
    _ = dyadicScale a := by
        simpa [used, eps] using two_pow_sub_mul_dyadicScale hae

/-- In a valid state, at most one slot matches a given client and son index pair. -/
private lemma grayTail_slot_matching_card_le_one
    {n b : ℕ} (st : GrayTailState n b)
    (hshape : GrayTailShape st) (i : Fin n) (c : Fin b) :
    (Finset.univ.filter (fun j : Fin st.slots.length =>
      decide ((st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c))).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro j1 j2 hj1 hj2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hj1 hj2
  have h_elem_eq : st.slots.get j1 = st.slots.get j2 := by
    have hr1 := hshape.slots_round (st.slots.get j1) (List.get_mem _ _)
    have hr2 := hshape.slots_round (st.slots.get j2) (List.get_mem _ _)
    rcases h1' : st.slots.get j1 with ⟨s1, c1, r1⟩
    rcases h2' : st.slots.get j2 with ⟨s2, c2, r2⟩
    rw [h1'] at hj1 hr1
    rw [h2'] at hj2 hr2
    have h1 : s1 = s2 := hj1.1.trans hj2.1.symm
    have h2 : c1 = c2 := hj1.2.trans hj2.2.symm
    have h3 : r1 = r2 := Fin.ext (hr1.trans hr2.symm)
    subst h1; subst h2; subst h3; rfl
  exact List.Nodup.get_inj_iff hshape.slots_nodup |>.mp h_elem_eq

/-- The active slot base contribution at state `t` is bounded by the call depth scale. -/
private lemma grayTailSlotSonBase_le_callScale
    {n q L a e t B : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hrun : GrayTailRunLegal n q L a e B sigma A sm)
    (hdone : (grayTailBranchStateAt n q L a e sigma A sm t).done = false)
    (hempty : (grayTailBranchStateAt n q L a e sigma A sm t).slots.isEmpty = false)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    grayTailSonBase (grayTailSlotEntries
      (grayTailBranchStateAt n q L a e sigma A sm t).slots
      (grayTailCurrentMove q L e sigma
        (grayTailBranchStateAt n q L a e sigma A sm t))) i c
      ≤ dyadicScale (grayCallDepth q e) := by
  obtain ⟨ha, hae, hB, hRung, hsm⟩ := hrun
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hdone : st.done = false := hdone
  have hempty : st.slots.isEmpty = false := hempty
  have hcert :=
    grayTailCertified_stateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have htrace :=
    grayTailTrace_stateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hhist :=
    grayTailHistoryOK_stateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hb : grayTailBaseBranch q L ≤ grayTailBranch q L a e := le_max_right _ _
  have hcount : st.frozen.length < grayTailRoundCount q := by
    by_contra h
    have hdone' := 
      grayTail_done_of_roundCount_stateAt_core (q := q) (L := L) (a := a) (e := e)
        (sigma := sigma) (A := A) (sm := sm) (t := t) (Nat.ge_of_not_lt h)
    change st.done = true at hdone'
    rw [hdone'] at hdone
    cases hdone
  have hlocal := grayTailFutureServer_legal hcert hcount hsm
  have hterm' : (st.done || st.slots.isEmpty) ≠ true := by
    simp [hdone, hempty]
  have hspec := grayTailRound_gameSpec ha hae hB hRung hcert hterm' hb
  rw [grayTailSonBase_slotEntries_eq_sum]
  have hlegal := hspec.weak.legal (grayTailFutureServer q L e st sm) hlocal
  have hcurr := grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace
  have h_elem : ∀ j : Fin st.slots.length,
    (if (st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c then
      getFamilyReq (grayTailCurrentMove q L e sigma st) j.val []
    else 0) ≤ dyadicScale (grayCallDepth q e) := by
    intro j
    split_ifs with hj
    · have hcoh := hlegal.1 st.history.2.length j.val j.isLt
      rw [hcurr]
      exact hcoh.2.1
    · exact (dyadicScale_pos (grayCallDepth q e)).le
  have hshape :=
    grayTailShape_stateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hcard := grayTail_slot_matching_card_le_one st hshape i c
  calc
    ∑ j : Fin st.slots.length,
      (if (st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c then
        getFamilyReq (grayTailCurrentMove q L e sigma st) j.val []
      else 0)
      ≤ ∑ j : Fin st.slots.length,
        if (st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c then
          dyadicScale (grayCallDepth q e)
        else 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : (st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c
        · rw [ite_eq_left hj, ite_eq_left hj]
          have hj' := h_elem j
          rw [ite_eq_left hj] at hj'
          exact hj'
        · rw [ite_eq_right hj, ite_eq_right hj]
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin st.slots.length =>
          decide ((st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c)),
          dyadicScale (grayCallDepth q e) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : (st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c
        · rw [ite_eq_left hj, ite_eq_left (decide_eq_true hj)]
        · rw [ite_eq_right hj, ite_eq_right (fun h => hj (decide_eq_true_iff.mp h))]
    _ = ((Finset.univ.filter (fun j : Fin st.slots.length =>
          decide ((st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c))).card : ℚ)
        * dyadicScale (grayCallDepth q e) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * dyadicScale (grayCallDepth q e) := by
        have hcard_Q : ((Finset.univ.filter (fun j : Fin st.slots.length =>
          decide ((st.slots.get j).1 = i ∧ (st.slots.get j).2.1 = c))).card : ℚ) ≤ 1 := by
          exact_mod_cast hcard
        nlinarith [hcard_Q, dyadicScale_pos (grayCallDepth q e)]
    _ = dyadicScale (grayCallDepth q e) := by ring

/-- Against a legal server play, every son base displayed by a tail run stays at most
`dyadicScale e`. -/
lemma grayTailSonBase_le_dyadicScale
    {n q L a e t B : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    grayTailSonBase (grayTailOutputEntries q L e sigma
      (grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)) i c
        ≤ dyadicScale e := by
  set st := grayTailStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  set entries := grayTailOutputEntries q L e sigma st
  by_cases hterm : (st.done || st.slots.isEmpty) = true
  · have hbase_eq : grayTailSonBase entries i c = grayTailFrozenSonBase st.frozen i c := by
      exact grayTail_terminal_sonBase_eq_frozen hterm i c
    have hbase : grayTailSonBase entries i c = grayTailFrozenSonBase st.frozen i c := hbase_eq
    rw [hbase]
    exact grayTail_all_frozen_base_le_stateAt q L a e sigma A sm t i c
  · have hnot : ¬ (st.done = true ∨ st.slots.isEmpty = true) := by
      rwa [Bool.or_eq_true] at hterm
    have hdone : st.done = false := 
      Bool.eq_false_iff.mpr (fun h => hnot (Or.inl (by exact h)))
    have hempty : st.slots.isEmpty = false := 
      Bool.eq_false_iff.mpr (fun h => hnot (Or.inr (by exact h)))
    have hfrozen_le : grayTailFrozenSonBase st.frozen i c ≤ dyadicScale e :=
      grayTail_all_frozen_base_le_stateAt q L a e sigma A sm t i c
    have hactive_le :=
      grayTail_active_base_le_stateAt_global (n := n) (b := grayTailBranch q L a
                                                        e) q L a e sigma A sm t
    have hcall_thresh := grayTail_callScale_add_threshold_le q e
    have hdone_not : ¬ st.done = true := by simp [hdone]
    change grayTailSonBase (grayTailEntries st.frozen st.slots
      (if st.done then [] else grayTailCurrentMove q L e sigma st)) i c ≤ dyadicScale e
    rw [ite_eq_right hdone_not, grayTailEntries, grayTailSonBase_append_globalEntries]
    by_cases hhas : GrayTailHasKey st.slots i c
    · obtain ⟨s, hs, hi, hc⟩ := hhas
      have hfrozen_thresh : grayTailFrozenSonBase st.frozen i c ≤
          dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
        simpa [hi, hc] using hactive_le s hs
      have hslot_le :=
        grayTailSlotSonBase_le_callScale ⟨ha, hae, hB, hRung, hsm⟩ hdone hempty i c
      change grayTailFrozenSonBase st.frozen i c
        + grayTailSonBase (grayTailSlotEntries st.slots
          (grayTailCurrentMove q L e sigma st)) i c ≤ dyadicScale e
      linarith [hfrozen_thresh, hslot_le, hcall_thresh]
    · have hslot_zero : grayTailSonBase (grayTailSlotEntries st.slots
          (grayTailCurrentMove q L e sigma st)) i c = 0 := by
        apply grayTailSonBase_eq_zero_of_not_hasKey
        exact hhas
      change grayTailFrozenSonBase st.frozen i c
        + grayTailSonBase (grayTailSlotEntries st.slots
          (grayTailCurrentMove q L e sigma st)) i c ≤ dyadicScale e
      rw [hslot_zero, add_zero]
      exact hfrozen_le

/-- Every move recorded in the frozen rounds is request coherent with cap
`dyadicScale (grayCallDepth q e)`. -/
def GrayTailFrozenCoherent {n b : ℕ} (q e : ℕ) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    requestCoherentCap b (dyadicScale (grayCallDepth q e)) (familyClientMoveAt p.move j)

end Kolmogorov
