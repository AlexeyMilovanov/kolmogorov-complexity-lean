import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Support
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvantageCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendCore

/-!
# The minimum-request field of the V2 charged outer strategy

Port of `grayCharged_output_avoidsSmall` (`GacsDayChargedClosureLeaves`) to
the V2 block controller: every request of the outer move displayed by
`grayChargedStrategyV2` is either zero or at least the common final fine scale
`dyadicScale (e + grayTailNewLoss q L)` — the `minimum_request` field of
`GrayChargedOuterFieldsV2`.

Every sub-move the controller displays is a play of the pinned child rung
against a legal local server: the current advantage move is the canonical play
of the block round strategy against the V2 future server
(`grayBlockCurrentMoveV2_eq_futurePlay`, legal by
`grayChargedBlockTailFutureServerV2_legal`), the current spend move is the
canonical play of the pass strategy against the spend future server
(`grayBlockSpendMoveV2_eq_futurePlay`, legal by
`grayChargedSpendFutureServerV2_legal`), and the rung's `minimum_request`
bounds both at the round's fine depth, which sits above `e + grayTailNewLoss q L`.
The invariant "every frozen round's move avoids small requests" is carried
along the certified run, and the generic graft lemmas finish exactly as in V1.
-/

namespace Kolmogorov

/-! ### Scale bounds -/

/-- Every spend pass's fine depth sits above the common final fine scale. -/
lemma grayChargedSpendDelta_le_newLoss {a e : ℕ} (hae : a ≤ e) (q L pass : ℕ) :
    grayChargedSpendDelta a L e pass ≤ e + grayTailNewLoss q L := by
  have hLle : L + 3 ≤ grayTailNewLoss q L := by
    rw [grayTailNewLoss_eq]
    have hq1 : 256 ≤ 256 * (q + 1) := by omega
    have hq2 : L ≤ 256 * (q + 1) ^ 2 * L := by
      have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
      calc
        L = 1 * L := (one_mul L).symm
        _ ≤ 256 * (q + 1) ^ 2 * L := Nat.mul_le_mul_right L hpos
    omega
  unfold grayChargedSpendDelta grayChargedSpendEps grayChargedSpendAlphaDepth
  omega

/-- Every advantage round's fine depth sits above the common final fine scale. -/
lemma grayTailRoundDelta_le_newLoss (q L e r : ℕ) :
    grayTailRoundDelta q L e r ≤ e + grayTailNewLoss q L := by
  simpa only [grayTailNewLoss, Nat.add_assoc] using grayTailRoundDelta_upper q L e r

/-- The empty family move avoids small requests at every root. -/
lemma requestAvoidsSmall_familyClientMoveAt_nil (delta : ℚ) (j : ℕ) :
    requestAvoidsSmall delta (familyClientMoveAt [] j) := by
  intro x
  simp [familyClientMoveAt, getReq]

/-! ### The current sub-moves avoid small requests -/

/-- The current advantage sub-move of an active V2 core avoids small requests:
the pinned rung's `minimum_request` for the block round strategy against the
legal V2 future server, transported through the replay identification. -/
lemma grayBlockCurrentMoveV2_avoidsSmall_of_legal
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hhist : GrayBlockHistoryOKV2 q L e sigma st)
    (htrace : GrayTailTraceV2 q L e sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayBlockFutureServerV2 q L e st sm))
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    familyRequestAvoidsSmall st.slots.length (dyadicScale (e + grayTailNewLoss q L))
      (grayBlockCurrentMoveV2 q L e sigma st) := by
  have hspec := (grayChargedBlockRound_gameSpecV2 ha hae hL hRung hactive).weak
  have hmin := hspec.minimum_request (grayBlockFutureServerV2 q L e st sm) hlocal
    st.history.2.length
  have hdelta_le := grayTailRoundDelta_le_newLoss q L e st.frozen.length
  rw [grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist htrace]
  intro j hj x
  rcases hmin j hj x with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr (le_trans (dyadicScale_antitone hdelta_le) hpositive)

/-- The current spend sub-move of a replay-consistent V2 spend core avoids
small requests: the pinned rung's `minimum_request` for the pass strategy
against the legal spend future server. -/
lemma grayBlockSpendMoveV2_avoidsSmall_of_legal
    {q L a e n t pass : ℕ} {sigma : FamilyStrategyScheme}
    {sm : ℕ → FamilyServerMove}
    (hae : a ≤ e) (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayChargedSpendFutureServerV2 a L e pass st sm))
    (hslots : st.slots.isEmpty = false) :
    familyRequestAvoidsSmall st.slots.length (dyadicScale (e + grayTailNewLoss q L))
      (grayBlockSpendMoveV2 q L a e pass sigma st) := by
  have hspec :=
    (grayChargedSpendRound_gameSpecV2 (st := st) (pass := pass) hL hRung hslots).weak
  have hmin := hspec.minimum_request (grayChargedSpendFutureServerV2 a L e pass st sm)
    hlocal st.history.2.length
  have hdelta_le := grayChargedSpendDelta_le_newLoss hae q L pass
  rw [grayBlockSpendMoveV2_eq_futurePlay hst]
  intro j hj x
  rcases hmin j hj x with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr (le_trans (dyadicScale_antitone hdelta_le) hpositive)

/-- At an advantage time of the V2 run with nonempty slots, the current
advantage sub-move avoids small requests. -/
lemma grayChargedRunStateV2_advantageMove_avoidsSmall
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = false)
    (hne : 1 ≤ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.length) :
    familyRequestAvoidsSmall
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayBlockCurrentMoveV2 q L e sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core) := by
  have hhist := grayChargedBlockHistoryOKV2_stateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have htrace := grayChargedBlockTailTraceV2_stateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  have hlocal := grayChargedBlockTailFutureServerV2_legal
    (grayChargedBlockTailCertifiedV2_stateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t) hsm
  have hcoreEq := grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm t hphase
  rw [hcoreEq] at hdone hne ⊢
  generalize grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = tl at hhist htrace hlocal hdone hne ⊢
  have hslots : tl.slots.isEmpty = false := by
    cases hs : tl.slots with
    | nil => simp [hs] at hne
    | cons _ _ => simp
  have hactive : (tl.done || tl.slots.isEmpty) ≠ true := by
    simp [hdone, hslots]
  exact grayBlockCurrentMoveV2_avoidsSmall_of_legal ha hae hL hRung tl hhist htrace
    hlocal hactive

/-- At a spend time of the V2 run, the current spend sub-move avoids small
requests. -/
lemma grayChargedRunStateV2_spendMove_avoidsSmall
    {q L a e n t pass : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hae : a ≤ e) (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass) :
    familyRequestAvoidsSmall
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length
      (dyadicScale (e + grayTailNewLoss q L))
      (grayBlockSpendMoveV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core) := by
  have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm t pass hphase
  have hcert := grayChargedRunStateV2_spendCertified_of_phase hphase
  exact grayBlockSpendMoveV2_avoidsSmall_of_legal hae hL hRung _ hok
    (grayChargedSpendFutureServerV2_legal hcert hsm) hcert.slots_nonempty

/-! ### The frozen-moves invariant along the certified run -/

/-- Every frozen V2 round stores a move which, at every local root, avoids
small requests at the common final fine scale. -/
def GrayChargedFrozenAvoidsSmallV2 {n b : ℕ} (q L e : ℕ)
    (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L)) (familyClientMoveAt p.move j)

/-- Freezing a round whose move avoids small requests keeps the V2 frozen rounds free of them. -/
lemma grayChargedFrozenAvoidsSmallV2_append {n b q L e : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenAvoidsSmallV2 q L e frozen) (p : GrayTailRoundV2 n b)
    (hp : ∀ j < p.slots.length,
      requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
        (familyClientMoveAt p.move j)) :
    GrayChargedFrozenAvoidsSmallV2 q L e (frozen ++ [p]) := by
  intro p' hp' j hj
  rcases List.mem_append.mp hp' with h | h
  · exact hst p' h j hj
  · rw [List.mem_singleton] at h
    subst h
    exact hp j hj

/-- The V1 projection of the ledger inherits the invariant (`toV1` keeps the
slots and the move). -/
lemma grayChargedFrozenAvoidsSmallV2_toV1 {n b q L e : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenAvoidsSmallV2 q L e frozen) :
    ∀ p ∈ frozen.map GrayTailRoundV2.toV1, ∀ j < p.slots.length,
      requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
        (familyClientMoveAt p.move j) := by
  intro p hp j hj
  rw [List.mem_map] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact hst p' hp' j hj

/-- The strict V2 advantage step preserves the invariant, given that the
current advantage sub-move avoids small requests whenever slots are nonempty. -/
lemma grayChargedBlockTailStepV2_frozen_avoidsSmall
    {q L a e n b : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayTailStateV2 n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenAvoidsSmallV2 q L e st.frozen)
    (hcur : 1 ≤ st.slots.length →
      familyRequestAvoidsSmall st.slots.length (dyadicScale (e + grayTailNewLoss q L))
        (grayBlockCurrentMoveV2 q L e sigma st)) :
    GrayChargedFrozenAvoidsSmallV2 q L e
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
        exact grayChargedFrozenAvoidsSmallV2_append hst _ (fun j hj => hcur hne j hj)
      · simpa [grayChargedBlockTailStepV2, hd', hs', hg] using hst

/-- The full V2 charged step preserves the invariant, given that the current
sub-move of the phase avoids small requests whenever slots are nonempty. -/
lemma grayChargedFrozenAvoidsSmallV2_step
    {q L a e n b : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayChargedStateV2 n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenAvoidsSmallV2 q L e st.core.frozen)
    (hcur : st.phase = .advantage → st.core.done = false → 1 ≤ st.core.slots.length →
      familyRequestAvoidsSmall st.core.slots.length
        (dyadicScale (e + grayTailNewLoss q L))
        (grayBlockCurrentMoveV2 q L e sigma st.core))
    (hcurSpend : ∀ pass, st.phase = .spend pass → 1 ≤ st.core.slots.length →
      familyRequestAvoidsSmall st.core.slots.length
        (dyadicScale (e + grayTailNewLoss q L))
        (grayBlockSpendMoveV2 q L a e pass sigma st.core)) :
    GrayChargedFrozenAvoidsSmallV2 q L e
      (grayChargedStepV2 q L a e sigma A st m).core.frozen := by
  cases hphase : st.phase with
  | done => simpa [grayChargedStepV2, hphase] using hst
  | advantage =>
      have hnext : GrayChargedFrozenAvoidsSmallV2 q L e
          (grayChargedBlockTailStepV2 q L a e sigma A st.core m).frozen := by
        by_cases hd : st.core.done = true
        · rw [grayChargedBlockTailStepV2_of_done q L a e sigma A st.core m hd]
          exact hst
        · have hd' : st.core.done = false := by simpa using hd
          exact grayChargedBlockTailStepV2_frozen_avoidsSmall (a := a) (A := A)
            st.core m hst (hcur hphase hd')
      simp only [grayChargedStepV2, hphase]
      by_cases hdone :
          (grayChargedBlockTailStepV2 q L a e sigma A st.core m).done = true
      · rw [if_pos hdone]
        by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A st.core m) m = true
        · rw [if_pos hserved, grayChargedStartSpendV2_frozen]
          exact hnext
        · rw [if_neg hserved]
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
        · have hcurP : ∀ j < st.core.slots.length,
              requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
                (familyClientMoveAt
                  (grayBlockSpendMoveV2 q L a e pass sigma st.core) j) :=
            fun j hj => hcurSpend pass hphase hne j hj
          simp only [grayChargedStepV2, hphase, hslots', Bool.false_eq_true,
            ↓reduceIte, hgoal]
          split
          · split
            · exact grayChargedFrozenAvoidsSmallV2_append hst _ hcurP
            · exact grayChargedFrozenAvoidsSmallV2_append hst _ hcurP
          · exact grayChargedFrozenAvoidsSmallV2_append hst _ hcurP
        · simpa [grayChargedStepV2, hphase, hslots', hgoal] using hst

/-- **The invariant along the V2 run**: every frozen round of the run state
stores a move avoiding small requests at the common final fine scale. -/
theorem grayChargedRunStateV2_frozen_avoidsSmall
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    GrayChargedFrozenAvoidsSmallV2 q L e
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen := by
  induction t with
  | zero =>
      intro p hp
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
        grayChargedInitialStateV2, grayChargedBlockTailInitialStateV2] at hp
  | succ t ih =>
      rw [grayChargedRunStateV2_succ]
      exact grayChargedFrozenAvoidsSmallV2_step _ (sm t) ih
        (fun hphase hd hne =>
          grayChargedRunStateV2_advantageMove_avoidsSmall ha hae hL hRung hsm hphase hd hne)
        (fun pass hphase _ =>
          grayChargedRunStateV2_spendMove_avoidsSmall hae hL hRung hsm hphase)

/-! ### The displayed move -/

/-- The displayed V2 move is the graft of the projected ledger, the active
slots and the current sub-move. -/
lemma grayChargedDisplayedMoveV2_eq_current {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (st : GrayChargedStateV2 n b) :
    grayChargedDisplayedMoveV2 q L a e sigma st =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (st.core.frozen.map GrayTailRoundV2.toV1)
        (if st.core.done then [] else st.core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma st) := by
  unfold grayChargedDisplayedMoveV2 grayChargedCurrentMoveV2
  obtain ⟨phase, core⟩ := st
  cases phase <;> rfl

/-- The current sub-move displayed by the V2 run avoids small requests at
every active slot. -/
lemma grayChargedRunStateV2_displayedCurrent_avoidsSmall
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    ∀ j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length,
      requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
        (familyClientMoveAt
          (grayChargedCurrentMoveV2 q L a e sigma
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) j) := by
  intro j hj
  have hne : 1 ≤ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.length := by omega
  unfold grayChargedCurrentMoveV2
  cases hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase with
  | advantage =>
      by_cases hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done = true
      · rw [if_pos (by simp [hd])]
        exact requestAvoidsSmall_familyClientMoveAt_nil _ j
      · have hd' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.done = false := by simpa using hd
        by_cases hempty : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots.isEmpty = true
        · rw [if_pos (by simp [hempty])]
          exact requestAvoidsSmall_familyClientMoveAt_nil _ j
        · have hempty' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core.slots.isEmpty = false := by simpa using hempty
          rw [if_neg (by simp [hd', hempty'])]
          exact grayChargedRunStateV2_advantageMove_avoidsSmall ha hae hL hRung hsm hphase
            hd' hne j hj
  | spend pass =>
      by_cases hempty : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots.isEmpty = true
      · simp only [hempty]
        exact requestAvoidsSmall_familyClientMoveAt_nil _ j
      · simp only [hempty]
        exact grayChargedRunStateV2_spendMove_avoidsSmall hae hL hRung hsm hphase j hj
  | done => exact requestAvoidsSmall_familyClientMoveAt_nil _ j

/-- The current sub-move avoids small requests at every displayed slot (none
on a done core). -/
lemma grayChargedRunStateV2_displayedCurrent_avoidsSmall_display
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    ∀ j < (if (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.done then []
      else (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots).length,
      requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L))
        (familyClientMoveAt
          (grayChargedCurrentMoveV2 q L a e sigma
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) j) := by
  intro j hj
  by_cases hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true
  · rw [if_pos hd] at hj
    simp at hj
  · rw [if_neg hd] at hj
    exact grayChargedRunStateV2_displayedCurrent_avoidsSmall ha hae hL hRung hsm t j hj

/-! ### The minimum-request field -/

/-- **Minimum request of the V2 charged outer strategy**: every request of the
displayed outer move is zero or at least the common final fine scale
`(1/2) ^ (e + grayTailNewLoss q L)`. -/
theorem grayChargedStrategyV2_avoidsSmall
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (sm : ℕ → FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ (e + grayTailNewLoss q L))
      (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t) := by
  intro i hi
  rw [playClientFamily_grayChargedStrategyV2, grayChargedDisplayedMoveV2_eq_current]
  have hfrozen := grayChargedFrozenAvoidsSmallV2_toV1
    (grayChargedRunStateV2_frozen_avoidsSmall ha hae hL hRung hsm t)
  have hcur := grayChargedRunStateV2_displayedCurrent_avoidsSmall_display ha hae hL hRung
    hsm t
  generalize grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hfrozen hcur ⊢
  have hall := grayChargedEntries_all_avoidsSmall hfrozen hcur
  have hdelta_e : dyadicScale (e + grayTailNewLoss q L) ≤ dyadicScale e :=
    dyadicScale_antitone (by omega)
  change requestAvoidsSmall (dyadicScale (e + grayTailNewLoss q L)) _
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hi]
  refine grayCharged_requestAvoidsSmall_graftTwoLevel ?_ ?_ ?_
  · exact grayChargedRootRequest_avoidsSmall (dyadicScale_pos _) hdelta_e hall
      (grayChargedSourceCount a e) (grayChargedThreshold q e) ⟨i, hi⟩
  · intro c hc
    rw [dif_pos hc]
    exact grayChargedSonRequest_avoidsSmall (dyadicScale_pos _) hdelta_e hall
      (grayChargedSourceCount a e) (grayChargedThreshold q e) ⟨i, hi⟩ ⟨c, hc⟩
  · intro c hc c' hc'
    rw [dif_pos hc, dif_pos hc']
    exact grayCharged_entryMove_avoidsSmall hall (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩)

end Kolmogorov
