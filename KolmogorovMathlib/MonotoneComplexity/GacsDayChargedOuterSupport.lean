import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayHarvest
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore

/-! Reachability support for charged outer game fields. -/

namespace Kolmogorov

/-- A client move supported by the charged construction: it requests nothing below a child index
`b` or more, and nothing at depth beyond `2 * q`. -/
def GrayChargedEntryMoveSupported (q b : ℕ) (m : ClientMove) : Prop :=
  (∀ (y : GacsDayNode) (j : ℕ), b ≤ j → getReq m (y ++ [j]) = 0) ∧
  (∀ y : GacsDayNode, 2 * q < y.length → getReq m y = 0)

/-- The empty client move is supported. -/
lemma grayChargedEntryMoveSupported_nil (q b : ℕ) :
    GrayChargedEntryMoveSupported q b [] := by
  constructor <;> intro _ _ <;> simp [getReq]

/-- A move assembled for a slot out of supported entries is again supported. -/
theorem grayCharged_entryMove_supported {n b : ℕ} {q : ℕ}
    {entries : List (GrayTailSlot n b × ClientMove)}
    (hall : ∀ pr ∈ entries, GrayChargedEntryMoveSupported q b pr.2)
    (slot : GrayTailSlot n b) :
    GrayChargedEntryMoveSupported q b (grayTailEntryMove entries slot) := by
  unfold grayTailEntryMove
  cases hfind : entries.find? (fun p => decide (p.1 = slot)) with
  | none => simpa using grayChargedEntryMoveSupported_nil q b
  | some pr =>
      have hmem : pr ∈ entries := List.mem_of_find?_eq_some hfind
      simpa using hall pr hmem

/-- The move a charged rung of the ladder plays in a recursive call is supported inside the
branching `grayTailBranch q L a e` and depth `2 * q`. -/
lemma grayCharged_rungMove_supported
    {q L B a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (r n' : ℕ) (hn' : 1 ≤ n') (hist : FamilyGameHistory)
    {j : ℕ} (hj : j < n') :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
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

/-- The branching the recursive call of a spend pass needs fits inside `grayTailBranch q L a e`. -/
lemma grayChargedSpendBranch_le
    {q L B a e : ℕ} (pass : ℕ)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L)) :
    ladderBranching B (grayChargedSpendAlphaDepth a)
        (grayChargedSpendEps a L e pass) ≤
      grayTailBranch q L a e := by
  have hexp : grayChargedSpendEps a L e pass -
      grayChargedSpendAlphaDepth a ≤ e - a := by
    unfold grayChargedSpendEps grayChargedSpendAlphaDepth
    omega
  have hpow : 2 * 2 ^ (grayChargedSpendEps a L e pass -
      grayChargedSpendAlphaDepth a) ≤ 2 * 2 ^ (e - a) :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hexp)
  have hsq : 0 < 256 * (q + 1) ^ 2 := by positivity
  have hL : L ≤ 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := by
    have h1 : 1 * L ≤ 256 * (q + 1) ^ 2 * L :=
      Nat.mul_le_mul_right L hsq
    omega
  have hinner : 256 * (q + 1) * 2 ^ L ≤
      256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hL)
  have hBbase : B ≤ grayTailBaseBranch q L := by
    rw [grayTailBaseBranch_eq_newBranch, grayTailNewLoss_eq]
    exact le_trans hB (max_le_max le_rfl hinner)
  unfold ladderBranching grayTailBranch
  exact max_le (le_trans hpow (le_max_left _ _))
    (le_trans hBbase (le_max_right _ _))

/-- The move a charged rung plays in the recursive call of a spend pass is supported inside the
branching `grayTailBranch q L a e` and depth `2 * q`. -/
lemma grayCharged_spendMove_supported
    {q L B a e : ℕ} {sigma : FamilyStrategyScheme} {A' : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (pass n' : ℕ) (hn' : 1 ≤ n') (hist : FamilyGameHistory)
    {j : ℕ} (hj : j < n') :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e)
      (familyClientMoveAt
        (sigma (grayChargedSpendAlphaDepth a)
          (grayChargedSpendEps a L e pass) A' n' hist) j) := by
  have hspec :=
    (hRung (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass)
      (by unfold grayChargedSpendAlphaDepth; omega)
      (le_max_left _ _) n' A' hn').weak
  have hbranch :
      ladderBranching B (grayChargedSpendAlphaDepth a)
          (grayChargedSpendEps a L e pass) ≤
        grayTailBranch q L a e := grayChargedSpendBranch_le pass hB
  constructor
  · intro y k hk
    exact hspec.range_supported hist y k (le_trans hbranch hk) j hj
  · intro y hy
    exact hspec.tree_supported hist y hy j hj

/-- The entries a charged state displays: its frozen rounds and slots together with the current
move of its phase. -/
def grayChargedOutputEntries {n b : ℕ} (q L a e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayChargedState n b) : List (GrayTailSlot n b × ClientMove) :=
  grayTailEntries st.core.frozen st.core.slots
    (match st.phase with
     | .done => []
     | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
     | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core)

/-- Every request in the active recursive move is either zero or at least the
common final fine scale. The semantic inputs are the weak game specification
and legality of the relocated server play supplied by the charged replay. -/
lemma grayChargedCurrentMove_avoidsSmall_of_legal
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hlocal : familyServerPlayLegal st.slots.length
      (grayTailBranch q L a e) st.unavailable
      (grayTailFutureServer q L e st sm))
    (hne : 1 <= st.slots.length) :
    familyRequestAvoidsSmall st.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayTailCurrentMove q L e sigma st) := by
  have hcall : 1 <= grayCallDepth q e := by
    unfold grayCallDepth
    omega
  have heps :
      grayCallDepth q e <=
        grayTailRoundEps q L e st.frozen.length :=
    grayTailRoundEps_lower q L e st.frozen.length
  have hbranch :
      ladderBranching B (grayCallDepth q e)
          (grayTailRoundEps q L e st.frozen.length) <=
        grayTailBranch q L a e :=
    le_trans (grayTailRecursiveBranch_le hB) (le_max_right _ _)
  have hspec := grayFamilyGameSpec_mono_branching hbranch
    (hRung (grayCallDepth q e)
      (grayTailRoundEps q L e st.frozen.length)
      hcall heps st.slots.length st.unavailable hne).weak
  have hmin := hspec.minimum_request
    (grayTailFutureServer q L e st sm) hlocal st.history.2.length
  rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
  intro j hj x
  cases hmin j hj x with
  | inl hzero =>
      apply Or.inl
      simpa [grayTailRoundStrategy] using hzero
  | inr hpositive =>
      have hdelta_le :
          grayTailRoundDelta q L e st.frozen.length <=
            e + grayTailNewLoss q L := by
        simpa only [grayTailNewLoss, Nat.add_assoc] using
          (grayTailRoundDelta_upper q L e st.frozen.length)
      apply Or.inr
      exact le_trans (dyadicScale_antitone hdelta_le)
        (by simpa [dyadicScale, grayTailRoundDelta, grayTailRoundStrategy] using
          hpositive)

/-- Every move recorded in the frozen rounds avoids requests smaller than
`dyadicScale (e + grayTailNewLoss q L)`. -/
def GrayChargedFrozenAvoidsSmall {n b : Nat}
    (q L e : Nat) (frozen : GrayTailFrozen n b) : Prop :=
  forall p, List.Mem p frozen -> forall j, j < p.slots.length ->
    requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
      (familyClientMoveAt p.move j)

/-- Freezing an advantage round whose current move avoids small requests keeps the frozen rounds
free of small requests. -/
lemma grayChargedFrozenAvoidsSmall_append
    {q L e n b : Nat} {sigma : FamilyStrategyScheme} {m : FamilyServerMove}
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenAvoidsSmall q L e st.frozen)
    (hcur : familyRequestAvoidsSmall st.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayTailCurrentMove q L e sigma st)) :
    GrayChargedFrozenAvoidsSmall q L e
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayTailRoundEps q L e st.frozen.length
           slots := st.slots
           move := grayTailCurrentMove q L e sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayTailRoundDelta q L e st.frozen.length) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  cases List.mem_append.mp hp with
  | inl hpOld =>
      exact hst p hpOld j hj
  | inr hpNew =>
      simp only [List.mem_singleton] at hpNew
      subst p
      exact hcur j hj

/-- Freezing a spend round whose move avoids small requests keeps the frozen rounds free of small
requests. -/
lemma grayChargedFrozenAvoidsSmall_append_spend
    {q L a e n b pass : Nat} {sigma : FamilyStrategyScheme}
    {m : FamilyServerMove}
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenAvoidsSmall q L e st.frozen)
    (hcur : familyRequestAvoidsSmall st.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayChargedSpendMove q L a e pass sigma st)) :
    GrayChargedFrozenAvoidsSmall q L e
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayChargedSpendEps a L e pass
           slots := st.slots
           move := grayChargedSpendMove q L a e pass sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayChargedSpendDelta a L e pass) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  cases List.mem_append.mp hp with
  | inl hpOld =>
      exact hst p hpOld j hj
  | inr hpNew =>
      simp only [List.mem_singleton] at hpNew
      subst p
      exact hcur j hj

/-- A tail step keeps the frozen rounds free of small requests, given that the current move
avoids them. -/
lemma grayChargedTailStep_frozen_avoidsSmall
    {q L a e n b : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayTailState n b)
    (hst : GrayChargedFrozenAvoidsSmall q L e st.frozen)
    (hcur : forall _hne : 1 <= st.slots.length,
      familyRequestAvoidsSmall st.slots.length
        (dyadicScale (e + grayTailNewLoss q L))
        (grayTailCurrentMove q L e sigma st))
    (m : FamilyServerMove) :
    GrayChargedFrozenAvoidsSmall q L e
      (grayChargedTailStep q L a e sigma A st m).frozen := by
  unfold grayChargedTailStep grayTailWaitingB
  dsimp only
  by_cases hd : st.done
  case pos =>
    rw [if_pos hd]
    exact hst
  case neg =>
    rw [if_neg hd]
    by_cases hempty : st.slots.isEmpty
    case pos =>
      rw [if_pos hempty]
      exact hst
    case neg =>
      rw [if_neg hempty]
      by_cases hgoal : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
      case pos =>
        rw [if_pos hgoal]
        have hne : 1 <= st.slots.length := by
          cases hs : st.slots with
          | nil => simp [hs] at hempty
          | cons x xs => exact Nat.succ_pos _
        exact grayChargedFrozenAvoidsSmall_append st hst (hcur hne)
      case neg =>
        rw [if_neg hgoal]
        exact hst

/-- A charged step keeps the frozen rounds free of small requests, given that the move of each
phase avoids them. -/
lemma grayChargedFrozenAvoidsSmall_step
    {q L a e n b : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayChargedState n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenAvoidsSmall q L e st.core.frozen)
    (hcur : st.phase = .advantage ->
      forall _hne : 1 <= st.core.slots.length,
        familyRequestAvoidsSmall st.core.slots.length
          (dyadicScale (e + grayTailNewLoss q L))
          (grayTailCurrentMove q L e sigma st.core))
    (hcurSpend : forall pass, st.phase = .spend pass ->
      1 <= st.core.slots.length ->
      familyRequestAvoidsSmall st.core.slots.length
        (dyadicScale (e + grayTailNewLoss q L))
        (grayChargedSpendMove q L a e pass sigma st.core)) :
    GrayChargedFrozenAvoidsSmall q L e
      (grayChargedStep q L a e sigma A st m).core.frozen := by
  unfold grayChargedStep
  cases hphase : st.phase with
  | done =>
      dsimp only
      exact hst
  | advantage =>
      dsimp only
      have hnext := grayChargedTailStep_frozen_avoidsSmall
        (a := a) (A := A) st.core hst (hcur hphase) m
      by_cases hdone :
          (grayChargedTailStep q L a e sigma A st.core m).done
      case pos =>
        rw [if_pos hdone]
        rw [grayChargedStartSpend_frozen]
        exact hnext
      case neg =>
        rw [if_neg hdone]
        exact hnext
  | spend pass =>
      dsimp only
      by_cases hempty : st.core.slots.isEmpty
      case pos =>
        rw [if_pos hempty]
        exact hst
      case neg =>
        rw [if_neg hempty]
        by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable
            (grayChargedSpendMove q L a e pass sigma st.core)
            (grayTailLocalServerMove
              (grayChargedSpendDelta a L e pass)
              st.core.slots m) = true
        case pos =>
          rw [if_pos hgoal]
          have hne : 1 <= st.core.slots.length := by
            cases hs : st.core.slots with
            | nil => simp [hs] at hempty
            | cons x xs => exact Nat.succ_pos _
          have happ := grayChargedFrozenAvoidsSmall_append_spend
            (pass := pass) st.core hst (hcurSpend pass hphase hne) (m := m)
          by_cases hpass : pass + 1 < 8
          case pos =>
            rw [if_pos hpass]
            by_cases hnextempty :
                (grayChargedSlotsForPass q a e (pass + 1)
                  (st.core.frozen ++
                    [{ roundIndex := st.core.frozen.length
                       serverTime := st.core.time
                       epsDepth := grayChargedSpendEps a L e pass
                       slots := st.core.slots
                       move := grayChargedSpendMove q L a e pass sigma st.core
                       allocated := grayTailLocalAllocatedList
                         (grayTailLocalServerMove
                           (grayChargedSpendDelta a L e pass)
                           st.core.slots m)
                       unavailable := st.core.unavailable }])).isEmpty
            case pos =>
              rw [if_pos hnextempty]
              exact happ
            case neg =>
              rw [if_neg hnextempty]
              exact happ
          case neg =>
            rw [if_neg hpass]
            exact happ
        case neg =>
          rw [if_neg hgoal]
          exact hst


/-- Every move recorded in the frozen rounds is supported: no request below a child index `b` or
more, none at depth beyond `2 * q`. -/
def GrayChargedFrozenSupported {n b : ℕ} (q : ℕ) (frozen : GrayTailFrozen n b) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    GrayChargedEntryMoveSupported q b (familyClientMoveAt p.move j)

/-- Freezing an advantage round keeps the frozen rounds supported. -/
lemma grayChargedFrozenSupported_append
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {m : FamilyServerMove}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hst : GrayChargedFrozenSupported q st.frozen)
    (hne : 1 ≤ st.slots.length) :
    GrayChargedFrozenSupported q
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayTailRoundEps q L e st.frozen.length
           slots := st.slots
           move := grayTailCurrentMove q L e sigma st
           allocated :=
             grayTailLocalAllocatedList (grayTailLocalServerMove (grayTailRoundDelta q L e
                                                                   st.frozen.length) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  rcases List.mem_append.mp hp with hp | hp
  · exact hst p hp j hj
  · simp only [List.mem_singleton] at hp
    subst hp
    dsimp only [grayTailCurrentMove]
    exact grayCharged_rungMove_supported hB hRung st.frozen.length st.slots.length hne st.history hj

/-- Freezing a spend round keeps the frozen rounds supported. -/
lemma grayChargedFrozenSupported_append_spend
    {q L B a e n pass : ℕ} {sigma : FamilyStrategyScheme} {m : FamilyServerMove}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hst : GrayChargedFrozenSupported q st.frozen)
    (hne : 1 ≤ st.slots.length) :
    GrayChargedFrozenSupported q
      (st.frozen ++
        [{ serverTime := st.time
           roundIndex := st.frozen.length
           epsDepth := grayChargedSpendEps a L e pass
           slots := st.slots
           move := grayChargedSpendMove q L a e pass sigma st
           allocated := grayTailLocalAllocatedList
             (grayTailLocalServerMove
               (grayChargedSpendDelta a L e pass) st.slots m)
           unavailable := st.unavailable }]) := by
  intro p hp j hj
  rcases List.mem_append.mp hp with hp | hp
  · exact hst p hp j hj
  · simp only [List.mem_singleton] at hp
    subst hp
    dsimp only [grayChargedSpendMove]
    exact grayCharged_spendMove_supported hB hRung pass st.slots.length hne
      st.history hj

/-- A tail step keeps the frozen rounds supported. -/
lemma grayChargedTailStep_frozen_supported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation} {m : FamilyServerMove}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hst : GrayChargedFrozenSupported q st.frozen) :
    GrayChargedFrozenSupported q (grayChargedTailStep q L a e sigma A st m).frozen := by
  unfold grayChargedTailStep grayTailWaitingB
  dsimp only
  by_cases hd : st.done
  · rw [if_pos hd]
    exact hst
  · rw [if_neg hd]
    by_cases hempty : st.slots.isEmpty
    · rw [if_pos hempty]
      exact hst
    · rw [if_neg hempty]
      by_cases hgoal : grayChargedTailGoalAtB q e (grayTailRoundEps q L e
                                                    st.frozen.length) (grayTailRoundDelta q L e
                                                                        st.frozen.length)
        st.slots.length st.unavailable (grayTailCurrentMove q L e sigma st) (grayTailLocalServerMove
                                                                              (grayTailRoundDelta q
                                                                                L e
        st.frozen.length) st.slots m) = true
      · rw [if_pos hgoal]
        have hne : 1 ≤ st.slots.length := by
          cases hs : st.slots <;> [simp [hs] at hempty; exact Nat.succ_pos _]
        exact grayChargedFrozenSupported_append hB hRung st hst hne
      · rw [if_neg hgoal]
        exact hst

/-- A charged step keeps the frozen rounds supported. -/
lemma grayChargedFrozenSupported_step
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayChargedState n (grayTailBranch q L a e)) (m : FamilyServerMove)
    (hst : GrayChargedFrozenSupported q st.core.frozen) :
    GrayChargedFrozenSupported q (grayChargedStep q L a e sigma A st m).core.frozen := by
  unfold grayChargedStep
  cases hphase : st.phase with
  | done =>
      dsimp only
      exact hst
  | advantage =>
      dsimp only
      have hnext := grayChargedTailStep_frozen_supported (A := A) hB hRung st.core hst (m := m)
      by_cases hdone : (grayChargedTailStep q L a e sigma A st.core m).done
      · rw [if_pos hdone]
        rw [grayChargedStartSpend_frozen]
        exact hnext
      · rw [if_neg hdone]
        exact hnext
  | spend pass =>
      dsimp only
      by_cases hempty : st.core.slots.isEmpty
      · rw [if_pos hempty]
        exact hst
      · rw [if_neg hempty]
        by_cases hgoal : grayChargedSpendGoalAtB q L a e pass st.core.slots.length
          st.core.unavailable (grayChargedSpendMove q L a e pass sigma
                                st.core) (grayTailLocalServerMove (grayChargedSpendDelta a L e
                                                                    pass) st.core.slots m) = true
        · rw [if_pos hgoal]
          have hne : 1 ≤ st.core.slots.length := by
            cases hs : st.core.slots <;> [simp [hs] at hempty; exact Nat.succ_pos _]
          by_cases hpass : pass + 1 < 8
          · rw [if_pos hpass]
            by_cases hnextempty :
              (grayChargedSlotsForPass q a e (pass + 1)
                  (st.core.frozen ++
                    [{ roundIndex := st.core.frozen.length, serverTime := st.core.time,
                       epsDepth := grayChargedSpendEps a L e pass, slots := st.core.slots,
                       move := grayChargedSpendMove q L a e pass sigma st.core,
                       allocated := grayTailLocalAllocatedList
                         (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                           st.core.slots m),
                       unavailable := st.core.unavailable }])).isEmpty
            · rw [if_pos hnextempty]
              exact grayChargedFrozenSupported_append_spend hB hRung st.core hst hne
            · rw [if_neg hnextempty]
              exact grayChargedFrozenSupported_append_spend hB hRung st.core hst hne
          · rw [if_neg hpass]
            exact grayChargedFrozenSupported_append_spend hB hRung st.core hst hne
        · rw [if_neg hgoal]
          exact hst

/-- At every time of a charged run the frozen rounds are supported. -/
lemma grayChargedFrozenSupported_stateAt
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (sm : ℕ → FamilyServerMove) :
    GrayChargedFrozenSupported q
      (grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm
        t).core.frozen := by
  induction t with
  | zero =>
      intro p hp
      simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
             grayChargedTailInitialState] at hp
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedFrozenSupported_step hB hRung _ (sm t) ih

/-- If the frozen moves and the current move are supported, so is every displayed entry of the
state. -/
lemma grayChargedEntries_all_supported {n b q : ℕ} {L a e : ℕ} {sigma : FamilyStrategyScheme}
    {st : GrayChargedState n b}
    (hfrozen : ∀ p ∈ st.core.frozen, ∀ j < p.slots.length,
      GrayChargedEntryMoveSupported q b (familyClientMoveAt p.move j))
    (hcur : ∀ j < st.core.slots.length,
      GrayChargedEntryMoveSupported q b (familyClientMoveAt
        (match st.phase with
          | .done => []
          | .advantage =>
            if st.core.slots.isEmpty then [] else grayTailCurrentMove q L e sigma st.core
          | .spend pass =>
            if st.core.slots.isEmpty then []
            else grayChargedSpendMove q L a e pass sigma st.core) j)) :
    ∀ pr ∈ grayChargedOutputEntries q L a e sigma st,
      GrayChargedEntryMoveSupported q b pr.2 := by
  intro pr hpr
  unfold grayChargedOutputEntries grayTailEntries at hpr
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

/-- Every entry displayed after replaying a history of server moves is supported. -/
lemma grayChargedFold_entries_supported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (history : List FamilyServerMove)
    (pr : GrayTailSlot n (grayTailBranch q L a e) × ClientMove)
    (hpr : pr ∈ grayChargedOutputEntries q L a e sigma
      (grayChargedFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A
        history)) :
    GrayChargedEntryMoveSupported q (grayTailBranch q L a e) pr.2 := by
  set st := grayChargedFold (n := n) (b := grayTailBranch q L a e) q L a e sigma A history
  refine grayChargedEntries_all_supported (st := st) ?_ ?_ pr hpr
  · set sm : ℕ → FamilyServerMove := fun i => history.getD i []
    have hfrozen := grayChargedFrozenSupported_stateAt (n := n) (A := A) (a := a) (e := e)
      hB hRung sm (t := history.length)
    have hst_eq : grayChargedStateAt (n := n) (b := grayTailBranch q L a
                                                e) q L a e sigma A sm history.length = st := by
      unfold grayChargedStateAt grayTailServerPrefix
      have hpref : (List.ofFn fun i : Fin history.length => sm i.val) = history := by
        ext i
        simp [sm, List.getD_eq_getElem?_getD]
      rw [hpref]
    rw [hst_eq] at hfrozen
    exact hfrozen
  · intro j hj
    rcases hphase : st.phase with _ | pass
    · by_cases hempty : st.core.slots.isEmpty
      · simp only [hempty]
        exact grayChargedEntryMoveSupported_nil q _
      · simp only [hempty]
        have hne : 1 ≤ st.core.slots.length := by
          cases hs : st.core.slots <;> [simp [hs] at hempty; exact Nat.succ_pos _]
        exact grayCharged_rungMove_supported hB hRung st.core.frozen.length st.core.slots.length hne
          st.core.history hj
    · by_cases hempty : st.core.slots.isEmpty
      · simp only [hempty]
        exact grayChargedEntryMoveSupported_nil q _
      · simp only [hempty]
        have hne : 1 ≤ st.core.slots.length := by
          cases hs : st.core.slots <;> [simp [hs] at hempty; exact Nat.succ_pos _]
        exact grayCharged_spendMove_supported hB hRung pass
          st.core.slots.length hne st.core.history hj
    · exact grayChargedEntryMoveSupported_nil q _

/-- The charged strategy only ever requests inside the branching `grayTailBranch q L a e`. -/
theorem grayChargedStrategy_rangeSupported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma) :
    FamilyRangeSupported n (grayTailBranch q L a e) A
      (grayChargedStrategy q L a e sigma) := by
  intro hist x i hi j hj
  set b := grayTailBranch q L a e
  set st := grayChargedFold (n := n) (b := b) q L a e sigma A hist.2
  set entries := grayChargedOutputEntries q L a e sigma st
  set source := grayChargedSourceCount a e
  set thresh := grayChargedThreshold q e
  set eps := dyadicScale e
  change getReq (familyClientMoveAt (grayChargedTailFamilyMove source thresh eps
      st.core.frozen st.core.slots
        (match st.phase with
          | .done => []
          | .advantage =>
            if st.core.slots.isEmpty then [] else grayTailCurrentMove q L e sigma st.core
          | .spend pass =>
            if st.core.slots.isEmpty then []
            else grayChargedSpendMove q L a e pass sigma st.core)) j) (x ++ [i]) = 0
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hj]
  refine getReq_graftTwoLevel_eq_zero_of_range ?_ x hi
  intro c hc c' hc' y k hk
  simp only [hc, hc', dif_pos]
  exact (grayCharged_entryMove_supported
    (fun pr hpr => grayChargedFold_entries_supported hB hRung hist.2 pr hpr) _).1 y k hk

/-- The charged strategy only ever requests at depth at most `2 * (q + 1)`. -/
theorem grayChargedStrategy_treeSupported
    {q L B a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma) :
    FamilyTreeSupported n (2 * (q + 1)) A (grayChargedStrategy q L a e sigma) := by
  intro hist x hx j hj
  set b := grayTailBranch q L a e
  set st := grayChargedFold (n := n) (b := b) q L a e sigma A hist.2
  set entries := grayChargedOutputEntries q L a e sigma st
  set source := grayChargedSourceCount a e
  set thresh := grayChargedThreshold q e
  set eps := dyadicScale e
  change getReq (familyClientMoveAt (grayChargedTailFamilyMove source thresh eps
      st.core.frozen st.core.slots
        (match st.phase with
          | .done => []
          | .advantage =>
            if st.core.slots.isEmpty then [] else grayTailCurrentMove q L e sigma st.core
          | .spend pass =>
            if st.core.slots.isEmpty then []
            else grayChargedSpendMove q L a e pass sigma st.core)) j) x = 0
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hj]
  refine getReq_graftTwoLevel_eq_zero_of_length (h := 2 * q) ?_ x (by omega)
  intro c hc c' hc' y hy
  simp only [hc, hc', dif_pos]
  exact (grayCharged_entryMove_supported
    (fun pr hpr => grayChargedFold_entries_supported hB hRung hist.2 pr hpr) _).2 y hy



/-! ### The coarse spend future server and its legality under room -/

/-- Along a traced history, the `j`-th recorded server move is the localisation of the outer move
at time `st.roundStart + j`. -/
lemma grayTailTraceAt_server_before {n b : ℕ}
    (delta : ℕ) {sm : ℕ → FamilyServerMove} {t : ℕ}
    {st : GrayTailState n b}
    (hst : GrayTailTraceAt delta sm t st)
    {j : ℕ} (hj : j < st.history.2.length) :
    grayTailServerOfList st.history.2 j =
      grayTailLocalServerMove delta st.slots (sm (st.roundStart + j)) := by
  have hget := congrArg
    (fun l : List FamilyServerMove => l.getD j [])
    hst.servers_eq
  unfold grayTailServerOfList
  rw [List.getD_eq_getElem _ _ hj]
  rw [← List.getD_eq_getElem st.history.2 [] hj]
  simpa [List.getD_eq_getElem?_getD, hj, List.getElem_ofFn] using hget

/-- The spend move of a pass is the move the recursive family play produces at the current
history length. -/
lemma grayChargedSpendMove_eq_futurePlay {n b : ℕ}
    (q L a e pass : ℕ) (sigma : FamilyStrategyScheme)
    {sm : ℕ → FamilyServerMove} {t : ℕ}
    {st : GrayTailState n b}
    (hhist : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := b) { phase := .spend pass, core := st })
    (htrace : GrayTailTraceAt (grayChargedSpendDelta a L e pass) sm t st) :
    grayChargedSpendMove q L a e pass sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayChargedRoundStrategy q L a e (.spend pass) sigma st)
        (grayChargedSpendFutureServer a L e pass st sm)
        st.history.2.length := by
  rw [grayChargedSpendMove_eq_play q L a e pass sigma st hhist]
  apply playClientFamily_congr_before
  intro j hj
  exact grayTailTraceAt_server_before _ htrace hj

/-- Outer legality of the truncated future server at an arbitrary local
depth, against the outer allocation alone. -/
lemma grayTailLocalFutureServer_legal_A {n b : ℕ}
    (delta : ℕ) {A : Allocation}
    {st : GrayTailState n b} (hnodup : st.slots.Nodup)
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b A
      (fun t => grayTailLocalServerMove delta st.slots
        (sm (st.roundStart + t))) := by
  have hshift :
      familyServerPlayLegal n b A
        (fun t => sm (st.roundStart + t)) := by
    simpa [Nat.add_comm] using
      familyServerPlayLegal_shift hsm st.roundStart
  unfold grayTailLocalServerMove
  exact familyServerPlayLegal_truncFamily
    (familyServerPlayLegal_inTreeFamily
      (serverPlayLegal_extractGrandchild st.slots hnodup
        hshift))

/-- **The coarse spend server is legal against the frozen unavailable
cells.**  Under room every spend delta is at least as coarse as every frozen
scale — the advantage rounds sit below the call depth and the earlier spend
passes sit exactly one telescope step higher — so a conflict forces
allocations of two distinct grandson slots to be comparable. -/
theorem grayChargedSpendFutureServer_legal {n b q L a e t pass : ℕ}
    {A : Allocation} {st : GrayTailState n b}
    {sm : ℕ → FamilyServerMove}
    (_hroom : a + 8 * L + 3 <= e)
    (_hpass : pass < 8)
    (hcore : GrayChargedCoreCertified q L a e A sm t st)
    (hsnap : st.unavailable =
      A ++ grayHarvest (grayChargedSpendDelta a L e pass) st.slots n
        (grayHarvestSnapshot sm
          (Option.map GrayTailRound.serverTime st.frozen.getLast?)))
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayChargedSpendFutureServer a L e pass st sm) := by
  have hnodup_all := hcore.all_slots_nodup
  obtain ⟨-, hnodup_slots, hdisjoint⟩ := List.nodup_append.mp hnodup_all
  have hA := grayTailLocalFutureServer_legal_A
    (grayChargedSpendDelta a L e pass) hnodup_slots hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  rw [hsnap]
  intro c hc a' ha'
  rcases List.mem_append.mp ha' with haA | haH
  · exact hA.2.2 u i hi x c hc a' haA
  · -- the harvest case (v14 §9.6): the shown cell lives inside its own
    -- slot's grandchild subtree at length ≤ spendDelta; the untouchable
    -- lemma kills comparability with every harvest entry.
    let newSlot : GrayTailSlot n b := st.slots.get ⟨i, hi⟩
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayChargedSpendDelta a L e pass) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayChargedSpendFutureServer] using hc
    have hx : forall d, d ∈ x -> d < b := by
      by_contra hbad
      have hz := getFamilyAlloc_grayTailLocalServerMove_of_not_mem
        (eps := grayChargedSpendDelta a L e pass)
        st.slots (sm (st.roundStart + u)) i hi x hbad
      rw [hz] at hcLocal
      simp at hcLocal
    have hcFull : c ∈ getFamilyAlloc (sm (st.roundStart + u)) newSlot.1.val
        (grayTailSlotNode newSlot ++ x) := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      have hextract := (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).1
      simpa [grayTailSlotNode, getFamilyAlloc] using hextract
    have hcLength :
        c.length <= grayChargedSpendDelta a L e pass := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).2
    have hnewMem : newSlot ∈ st.slots := List.get_mem st.slots ⟨i, hi⟩
    have hx' : forall d, d ∈ grayTailSlotNode newSlot ++ x -> d < b := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_cons.mp hd with hd | hd
        · exact hd ▸ newSlot.2.1.isLt
        · have hde : d = newSlot.2.2.val := by simpa using hd
          exact hde ▸ newSlot.2.2.isLt
      · exact hx d hd
    cases hlast : st.frozen.getLast? with
    | none =>
        rw [hlast] at haH
        simp [grayHarvestSnapshot, grayHarvest_nil] at haH
    | some pLast =>
        rw [hlast] at haH
        simp only [Option.map_some, grayHarvestSnapshot] at haH
        exact grayHarvest_untouchable hsm hnewMem hx' hcFull hcLength haH

/-- Along a certified history and a legal localised play, the spend move requests nothing below
`dyadicScale (e + grayTailNewLoss q L)`. -/
lemma grayChargedSpendMove_avoidsSmall_of_legal
    {q L B a e n t pass : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (st : GrayTailState n (grayTailBranch q L a e))
    (hhist : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass, core := st })
    (htrace : GrayTailTraceAt (grayChargedSpendDelta a L e pass) sm t st)
    (hlocal : familyServerPlayLegal st.slots.length
      (grayTailBranch q L a e) st.unavailable
      (grayChargedSpendFutureServer a L e pass st sm))
    (hne : 1 <= st.slots.length) :
    familyRequestAvoidsSmall st.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayChargedSpendMove q L a e pass sigma st) := by
  have hspec := grayFamilyGameSpec_mono_branching
    (grayChargedSpendBranch_le pass hB)
    (hRung (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass)
      (by unfold grayChargedSpendAlphaDepth; omega)
      (le_max_left _ _) st.slots.length st.unavailable hne).weak
  have hmin := hspec.minimum_request
    (grayChargedSpendFutureServer a L e pass st sm) hlocal
    st.history.2.length
  rw [grayChargedSpendMove_eq_futurePlay q L a e pass sigma hhist htrace]
  intro j hj x
  cases hmin j hj x with
  | inl hzero =>
      apply Or.inl
      simpa [grayChargedRoundStrategy] using hzero
  | inr hpositive =>
      have hLle : L + 3 <= grayTailNewLoss q L := by
        rw [grayTailNewLoss_eq]
        have hq1 : 256 <= 256 * (q + 1) := by
          calc
            256 = 256 * 1 := (mul_one 256).symm
            _ <= 256 * (q + 1) :=
              Nat.mul_le_mul_left 256 (Nat.succ_le_succ (Nat.zero_le q))
        have hq2 : L <= 256 * (q + 1) ^ 2 * L := by
          have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
          calc
            L = 1 * L := (one_mul L).symm
            _ <= 256 * (q + 1) ^ 2 * L := Nat.mul_le_mul_right L hpos
        omega
      have hdelta_le :
          grayChargedSpendDelta a L e pass <= e + grayTailNewLoss q L := by
        unfold grayChargedSpendDelta grayChargedSpendEps
          grayChargedSpendAlphaDepth
        omega
      apply Or.inr
      exact le_trans (dyadicScale_antitone hdelta_le)
        (by simpa [dyadicScale, grayChargedRoundStrategy] using
          hpositive)

end Kolmogorov
