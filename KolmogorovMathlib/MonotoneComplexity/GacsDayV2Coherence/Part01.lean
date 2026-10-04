import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.RootIncrements
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvantageCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Support
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Minimum
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence

/-!
# Gacs-Day coherence, part 1

Scale bounds for the coherence argument of the Gacs-Day construction.
-/

namespace Kolmogorov

/-! ### Scale bounds -/

/-- Every advantage anchor scale sits below the spend scale. -/
lemma grayTailRoundEps_scale_le_spendAlpha {q L a e : ℕ} (hae : a ≤ e) (r : ℕ) :
    dyadicScale (grayTailRoundEps q L e r) ≤
      dyadicScale (grayChargedSpendAlphaDepth a) :=
  le_trans (dyadicScale_antitone (grayTailRoundEps_lower q L e r))
    (grayChargedCallScale_le_spendAlpha hae)

/-- Every pass anchor scale sits below the spend scale. -/
lemma grayChargedSpendEps_scale_le_spendAlpha (a L e pass : ℕ) :
    dyadicScale (grayChargedSpendEps a L e pass) ≤
      dyadicScale (grayChargedSpendAlphaDepth a) :=
  dyadicScale_antitone (le_max_left _ _)

/-- The empty family move is coherent at every nonnegative cap. -/
lemma requestCoherentCap_familyClientMoveAt_nil (b : ℕ) {alpha : ℚ}
    (halpha : 0 ≤ alpha) (j : ℕ) :
    requestCoherentCap b alpha (familyClientMoveAt [] j) := by
  simp [requestCoherentCap, familyClientMoveAt, getReq, halpha]

/-! ### The current sub-moves are coherent -/

/-- The current advantage sub-move of an active V2 core is coherent at the
round's anchor scale: the pinned rung's `legal` for the block round strategy
against the legal V2 future server, transported through the replay
identification. -/
lemma grayBlockCurrentMoveV2_coherent_of_legal
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hhist : GrayBlockHistoryOKV2 q L e sigma st)
    (htrace : GrayTailTraceV2 q L e sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayBlockFutureServerV2 q L e st sm))
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    ∀ j < st.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayTailRoundEps q L e st.frozen.length))
        (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma st) j) := by
  have hspec := (grayChargedBlockRound_gameSpecV2 ha hae hL hRung hactive).weak
  have hlegal := hspec.legal (grayBlockFutureServerV2 q L e st sm) hlocal
  intro j hj
  rw [grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist htrace]
  exact hlegal.1 st.history.2.length j hj

/-- The current spend sub-move of a replay-consistent V2 spend core is
coherent at the pass anchor scale. -/
lemma grayBlockSpendMoveV2_coherent_of_legal
    {q L a e n t pass : ℕ} {sigma : FamilyStrategyScheme}
    {sm : ℕ → FamilyServerMove}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (st : GrayTailStateV2 n (grayTailBranch q L a e))
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st)
    (hlocal : familyServerPlayLegal st.slots.length (grayTailBranch q L a e)
      st.unavailable (grayChargedSpendFutureServerV2 a L e pass st sm))
    (hslots : st.slots.isEmpty = false) :
    ∀ j < st.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendEps a L e pass))
        (familyClientMoveAt (grayBlockSpendMoveV2 q L a e pass sigma st) j) := by
  have hspec :=
    (grayChargedSpendRound_gameSpecV2 (st := st) (pass := pass) hL hRung hslots).weak
  have hlegal := hspec.legal (grayChargedSpendFutureServerV2 a L e pass st sm) hlocal
  intro j hj
  rw [grayBlockSpendMoveV2_eq_futurePlay hst]
  exact hlegal.1 st.history.2.length j hj

/-- At an active advantage time of the V2 run with nonempty slots, the current
advantage sub-move is coherent at the round's anchor scale (in the
raised-service wait the core is done and no current sub-move is displayed). -/
lemma grayChargedRunStateV2_advantageMove_coherent
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
    ∀ j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayTailRoundEps q L e
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.frozen.length))
        (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) j) := by
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
  exact grayBlockCurrentMoveV2_coherent_of_legal ha hae hL hRung tl hhist htrace
    hlocal hactive

/-- At a spend time of the V2 run, the current spend sub-move is coherent at
the pass anchor scale. -/
lemma grayChargedRunStateV2_spendMove_coherent
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hL : L = grayFootprint q) (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (pass : ℕ)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass) :
    ∀ j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendEps a L e pass))
        (familyClientMoveAt (grayBlockSpendMoveV2 q L a e pass sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) j) := by
  have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm t pass hphase
  have hcert := grayChargedRunStateV2_spendCertified_of_phase hphase
  exact grayBlockSpendMoveV2_coherent_of_legal hL hRung _ hok
    (grayChargedSpendFutureServerV2_legal hcert hsm) hcert.slots_nonempty

/-! ### The frozen-moves invariant along the certified run -/

/-- Every frozen V2 round stores a move which, at every local root, is
coherent at the spend scale `dyadicScale (grayChargedSpendAlphaDepth a)`. -/
def GrayChargedFrozenCoherentV2 {n b : ℕ} (a : ℕ)
    (frozen : List (GrayTailRoundV2 n b)) : Prop :=
  ∀ p ∈ frozen, ∀ j < p.slots.length,
    requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
      (familyClientMoveAt p.move j)

/-- Freezing a round whose move is request coherent keeps the V2 frozen rounds coherent. -/
lemma grayChargedFrozenCoherentV2_append {n b a : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenCoherentV2 a frozen) (p : GrayTailRoundV2 n b)
    (hp : ∀ j < p.slots.length,
      requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt p.move j)) :
    GrayChargedFrozenCoherentV2 a (frozen ++ [p]) := by
  intro p' hp' j hj
  rcases List.mem_append.mp hp' with h | h
  · exact hst p' h j hj
  · rw [List.mem_singleton] at h
    subst h
    exact hp j hj

/-- The V1 projection of the ledger inherits the invariant (`toV1` keeps the
slots and the move). -/
lemma grayChargedFrozenCoherentV2_toV1 {n b a : ℕ}
    {frozen : List (GrayTailRoundV2 n b)}
    (hst : GrayChargedFrozenCoherentV2 a frozen) :
    ∀ p ∈ frozen.map GrayTailRoundV2.toV1, ∀ j < p.slots.length,
      requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt p.move j) := by
  intro p hp j hj
  rw [List.mem_map] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact hst p' hp' j hj

/-- The strict V2 advantage step preserves the invariant, given that the
current advantage sub-move of an active core is coherent whenever slots are
nonempty (a done core only ticks). -/
lemma grayChargedBlockTailStepV2_frozen_coherent
    {q L a e n b : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayTailStateV2 n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenCoherentV2 a st.frozen)
    (hcur : st.done = false → 1 ≤ st.slots.length → ∀ j < st.slots.length,
      requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma st) j)) :
    GrayChargedFrozenCoherentV2 a
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
        exact grayChargedFrozenCoherentV2_append hst _ (fun j hj => hcur hd' hne j hj)
      · simpa [grayChargedBlockTailStepV2, hd', hs', hg] using hst

/-- The full V2 charged step preserves the invariant, given that the current
sub-move of the phase is coherent whenever slots are nonempty (on an active
core in the advantage phase: the raised-service wait and its exit keep the
ledger). -/
lemma grayChargedFrozenCoherentV2_step
    {q L a e n b : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayChargedStateV2 n b) (m : FamilyServerMove)
    (hst : GrayChargedFrozenCoherentV2 a st.core.frozen)
    (hcur : st.phase = .advantage → st.core.done = false → 1 ≤ st.core.slots.length →
      ∀ j < st.core.slots.length,
        requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
          (familyClientMoveAt (grayBlockCurrentMoveV2 q L e sigma st.core) j))
    (hcurSpend : ∀ pass, st.phase = .spend pass → 1 ≤ st.core.slots.length →
      ∀ j < st.core.slots.length,
        requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
          (familyClientMoveAt (grayBlockSpendMoveV2 q L a e pass sigma st.core) j)) :
    GrayChargedFrozenCoherentV2 a
      (grayChargedStepV2 q L a e sigma A st m).core.frozen := by
  cases hphase : st.phase with
  | done => simpa [grayChargedStepV2, hphase] using hst
  | advantage =>
      have hnext := grayChargedBlockTailStepV2_frozen_coherent (a := a) (A := A)
        st.core m hst (hcur hphase)
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
        · have hcurP : ∀ j < st.core.slots.length,
              requestCoherentCap b (dyadicScale (grayChargedSpendAlphaDepth a))
                (familyClientMoveAt
                  (grayBlockSpendMoveV2 q L a e pass sigma st.core) j) :=
            fun j hj => hcurSpend pass hphase hne j hj
          simp only [grayChargedStepV2, hphase, hslots', Bool.false_eq_true,
            ↓reduceIte, hgoal]
          split
          · split
            · exact grayChargedFrozenCoherentV2_append hst _ hcurP
            · exact grayChargedFrozenCoherentV2_append hst _ hcurP
          · exact grayChargedFrozenCoherentV2_append hst _ hcurP
        · simpa [grayChargedStepV2, hphase, hslots', hgoal] using hst

/-- **The invariant along the V2 run**: every frozen round of the run state
stores a move coherent at the spend scale. -/
theorem grayChargedRunStateV2_frozen_coherent
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    GrayChargedFrozenCoherentV2 a
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen := by
  induction t with
  | zero =>
      intro p hp
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
        grayChargedInitialStateV2, grayChargedBlockTailInitialStateV2] at hp
  | succ t ih =>
      rw [grayChargedRunStateV2_succ]
      exact grayChargedFrozenCoherentV2_step _ (sm t) ih
        (fun hphase hdone hne j hj =>
          (grayChargedRunStateV2_advantageMove_coherent ha hae hL hRung hsm hphase hdone
            hne j hj).mono_cap (grayTailRoundEps_scale_le_spendAlpha hae _))
        (fun pass hphase _ j hj =>
          (grayChargedRunStateV2_spendMove_coherent hL hRung hsm pass hphase
            j hj).mono_cap (grayChargedSpendEps_scale_le_spendAlpha a L e pass))

/-! ### The displayed entries are coherent -/

/-- The current sub-move displayed by the V2 run is coherent at the spend
scale at every active slot. -/
lemma grayChargedRunStateV2_displayedCurrent_coherent
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    ∀ j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt
          (grayChargedCurrentMoveV2 q L a e sigma
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) j) := by
  intro j hj
  have hne : 1 ≤ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.length := by omega
  have hpos : (0 : ℚ) ≤ dyadicScale (grayChargedSpendAlphaDepth a) :=
    (dyadicScale_pos _).le
  unfold grayChargedCurrentMoveV2
  cases hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase with
  | advantage =>
      by_cases hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done = true
      · rw [ite_eq_left (by simp [hd])]
        exact requestCoherentCap_familyClientMoveAt_nil _ hpos j
      · have hd' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.done = false := by simpa using hd
        by_cases hempty : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots.isEmpty = true
        · rw [ite_eq_left (by simp [hempty])]
          exact requestCoherentCap_familyClientMoveAt_nil _ hpos j
        · have hempty' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core.slots.isEmpty = false := by simpa using hempty
          rw [ite_eq_right (by simp [hd', hempty'])]
          exact (grayChargedRunStateV2_advantageMove_coherent ha hae hL hRung hsm hphase
            hd' hne j hj).mono_cap (grayTailRoundEps_scale_le_spendAlpha hae _)
  | spend pass =>
      by_cases hempty : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots.isEmpty = true
      · simp only [hempty]
        exact requestCoherentCap_familyClientMoveAt_nil _ hpos j
      · simp only [hempty]
        exact (grayChargedRunStateV2_spendMove_coherent hL hRung hsm pass hphase
          j hj).mono_cap (grayChargedSpendEps_scale_le_spendAlpha a L e pass)
  | done => exact requestCoherentCap_familyClientMoveAt_nil _ hpos j

/-- The current sub-move is coherent at the spend scale at every displayed
slot (none on a done core: the raised-service wait and the done phase display
the frozen ledger only). -/
lemma grayChargedRunStateV2_displayedCurrent_coherent_display
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    ∀ j < (if (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.done then []
      else (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots).length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt
          (grayChargedCurrentMoveV2 q L a e sigma
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t)) j) := by
  intro j hj
  by_cases hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true
  · rw [ite_eq_left hd] at hj
    simp at hj
  · rw [ite_eq_right hd] at hj
    exact grayChargedRunStateV2_displayedCurrent_coherent ha hae hL hRung hsm t j hj

/-- All entries of a projected ledger with a coherent current move are
coherent. -/
lemma grayChargedV2_entries_all_coherent {n b : ℕ} {alpha : ℚ}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (hfrozen : ∀ p ∈ frozen, ∀ j < p.slots.length,
      requestCoherentCap b alpha (familyClientMoveAt p.move j))
    (hcur : ∀ j < slots.length,
      requestCoherentCap b alpha (familyClientMoveAt current j)) :
    ∀ pr ∈ grayTailEntries frozen slots current, requestCoherentCap b alpha pr.2 := by
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

/-- **Every displayed entry of the V2 run is coherent** at the spend scale
(the displayed slots are the active slots, none on a done core). -/
theorem grayChargedRunStateV2_entries_coherent
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) (t : ℕ) :
    ∀ pr ∈ grayTailEntries
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)
        (if (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done then []
        else (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t)),
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a)) pr.2 :=
  grayChargedV2_entries_all_coherent
    (grayChargedFrozenCoherentV2_toV1
      (grayChargedRunStateV2_frozen_coherent ha hae hL hRung hsm t))
    (grayChargedRunStateV2_displayedCurrent_coherent_display ha hae hL hRung hsm t)

/-! ### The source son-base cap of the displayed entries -/

/-- The son base of the current move's slot entries in a wide-block fibre is
at most the call scale, from the per-root cap at the round anchor and the
block multiplicity (the cap-based form of the son-base keystone). -/
lemma grayChargedBlockCurrentSonBase_le_callScale {n b q L e r : ℕ}
    {slots : List (GrayTailSlot n b)} {move : FamilyClientMove}
    (hcap : ∀ j < slots.length,
      getReq (familyClientMoveAt move j) [] ≤ dyadicScale (grayTailRoundEps q L e r))
    (hcount : ∀ (i : Fin n) (c : Fin b),
      (slots.filter fun s => decide (s.1 = i ∧ s.2.1 = c)).length ≤
        grayAdvBlockMult q L r)
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (grayTailSlotEntries slots move) i c ≤
      dyadicScale (grayCallDepth q e) := by
  set α := dyadicScale (grayTailRoundEps q L e r) with hα
  have hαnn : (0 : ℚ) ≤ α := (dyadicScale_pos _).le
  set es := grayTailSlotEntries slots move with hes
  rw [grayTailSonBase_eq_sum_map_l4]
  have hle : (es.map fun z => if z.1.1 = i ∧ z.1.2.1 = c then getReq z.2 [] else 0).sum ≤
      (es.map fun z => if z.1.1 = i ∧ z.1.2.1 = c then α else 0).sum := by
    apply List.sum_le_sum
    intro z hz
    by_cases hm : z.1.1 = i ∧ z.1.2.1 = c
    · simp only [ite_eq_left hm]
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz
      rw [← hj]
      exact hcap j.val j.isLt
    · simp [ite_eq_right hm]
  refine le_trans hle ?_
  rw [sum_map_ite_eq_countP es (fun z => z.1.1 = i ∧ z.1.2.1 = c) α]
  have hmapfst : es.map Prod.fst = slots := by
    rw [hes, grayTailSlotEntries, List.map_ofFn]
    exact List.ofFn_get slots
  have hcountP : (es.countP fun z => decide (z.1.1 = i ∧ z.1.2.1 = c)) =
      (slots.filter fun sl => decide (sl.1 = i ∧ sl.2.1 = c)).length := by
    have : (es.countP fun z => decide (z.1.1 = i ∧ z.1.2.1 = c)) =
        (es.map Prod.fst).countP fun sl => decide (sl.1 = i ∧ sl.2.1 = c) := by
      rw [List.countP_map]
      rfl
    rw [this, hmapfst, List.countP_eq_length_filter]
  rw [hcountP]
  have hcnt := hcount i c
  calc α * ((slots.filter fun sl => decide (sl.1 = i ∧ sl.2.1 = c)).length : ℚ)
      ≤ α * (grayAdvBlockMult q L r : ℚ) := by
        apply mul_le_mul_of_nonneg_left ?_ hαnn
        exact_mod_cast hcnt
    _ = dyadicScale (grayCallDepth q e) := by
        rw [hα, mul_comm]
        exact grayAdvBlock_fibre_mass q L e r

/-- Appending a round whose slots only use spare sons keeps every source
son base of the frozen ledger. -/
lemma grayTailFrozenSonBase_append_spare {n b source : ℕ}
    (frozen : GrayTailFrozen n b) (p : GrayTailRound n b)
    (hspare : ∀ s ∈ p.slots, source ≤ s.2.1.val)
    (i : Fin n) (c : Fin b) (hc : c.val < source) :
    grayTailFrozenSonBase (frozen ++ [p]) i c = grayTailFrozenSonBase frozen i c := by
  rw [grayTailFrozenSonBase_append_global]
  have hzero : grayTailSonBase (grayTailSlotEntries p.slots p.move) i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro z hz
    rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    right
    intro heq
    have hge := hspare (p.slots.get j) (List.get_mem _ _)
    have hval : (p.slots.get j).2.1.val = c.val := congrArg Fin.val heq
    omega
  rw [hzero, add_zero]

/-- The V2 charged step from an advantage state over a done core (the
raised-service wait) keeps the frozen ledger: the strict step only ticks the
clock, and the exit `grayChargedStartSpendV2` keeps the ledger. -/
lemma grayChargedStepV2_frozen_of_wait {n b : ℕ} (q L a e : ℕ)
    (sigma : FamilyStrategyScheme) (A : Allocation) (core : GrayTailStateV2 n b)
    (m : FamilyServerMove) (hdone : core.done = true) :
    (grayChargedStepV2 q L a e sigma A { phase := .advantage, core := core } m).core.frozen =
      core.frozen := by
  have htick := grayChargedBlockTailStepV2_of_done q L a e sigma A core m hdone
  have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core m).done = true := by
    rw [htick]
    exact hdone
  have hphase : ({ phase := .advantage, core := core } : GrayChargedStateV2 n b).phase =
      .advantage := rfl
  by_cases hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A core m) m = true
  · rw [grayChargedStepV2_advantage_exit q L a e sigma A { phase := .advantage, core := core }
      m hphase hnd hserved, grayChargedStartSpendV2_frozen, htick]
  · have hserved' : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A core m) m = false := by
      simpa using hserved
    rw [grayChargedStepV2_advantage_wait q L a e sigma A { phase := .advantage, core := core }
      m hphase hnd hserved', htick]

/-- The source son bases of the projected frozen ledger are capped by one
coarse unit `dyadicScale e`. -/
def GrayChargedSourceBaseCapV2 {n b : ℕ} (a e : ℕ) (st : GrayChargedStateV2 n b) : Prop :=
  ∀ i : Fin n, ∀ c : Fin b, c.val < grayChargedSourceCount a e →
    grayTailFrozenSonBase (st.core.frozen.map GrayTailRoundV2.toV1) i c ≤ dyadicScale e

/-- **The source son-base cap along the V2 run**: the advantage prefix is
capped through the wide-block keystone, and the spend rounds only occupy
spare sons. -/
theorem grayChargedSourceBaseCapV2_stateAt
    {q L a e n : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove} (t : ℕ) :
    GrayChargedSourceBaseCapV2 a e
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      intro i c _
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
        grayChargedInitialStateV2, grayChargedBlockTailInitialStateV2,
        grayTailFrozenSonBase, grayTailFrozenEntries, grayTailSonBase,
        (dyadicScale_pos e).le]
  | succ t ih =>
      rw [grayChargedRunStateV2_succ]
      have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
      generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hcert ih ⊢
      cases hcert with
      | advantage core hcore hsource hactive =>
          have hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).phase = .advantage := by
            rw [hst]
          have hcoreTail := grayChargedRunStateV2_core_eq_tailStateAt
            q L a e sigma A sm t hphase
          have hcoreTail' : core = grayChargedBlockTailStateAtV2
              (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t := by
            simpa [hst] using hcoreTail
          have hnextAll := grayChargedBlockV2_all_frozen_base_le_stateAt (n := n)
            q L a e sigma A sm (t + 1)
          rw [grayChargedBlockTailStateAtV2_succ, ← hcoreTail'] at hnextAll
          intro i c _
          by_cases hdone :
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
          · by_cases hserved : grayChargedWaitServedB q a e
                (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
            · simpa [grayChargedStepV2, hdone, hserved, grayChargedStartSpendV2_frozen,
                frozenV1OfV2] using hnextAll i c
            · simpa [grayChargedStepV2, hdone, hserved, frozenV1OfV2] using hnextAll i c
          · simpa [grayChargedStepV2, hdone, frozenV1OfV2] using hnextAll i c
      | wait core hcore hsource hdone =>
          intro i c hc
          rw [grayChargedStepV2_frozen_of_wait q L a e sigma A core (sm t) hdone]
          exact ih i c hc
      | spend pass core hspend =>
          intro i c hc
          have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
          by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
              core.slots.length core.unavailable
              (grayBlockSpendMoveV2 q L a e pass sigma core)
              (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                core.slots (sm t)) = true
          · have hspare : ∀ s ∈ core.slots, grayChargedSourceCount a e ≤ s.2.1.val := by
              intro s hs
              rw [hspend.slots_eq] at hs
              exact grayBlockSpendSlotsV2_son_ge
                (by simpa [grayChargedSlotsForPassV2] using hs)
            have key : ∀ p : GrayTailRoundV2 n (grayTailBranch q L a e),
                p.slots = core.slots →
                grayTailFrozenSonBase ((core.frozen ++ [p]).map GrayTailRoundV2.toV1)
                  i c ≤ dyadicScale e := by
              intro p hp
              rw [List.map_append, List.map_cons, List.map_nil,
                grayTailFrozenSonBase_append_spare (source := grayChargedSourceCount a e)
                  _ _ (by
                    intro s hs
                    simp only [GrayTailRoundV2.toV1] at hs
                    rw [hp] at hs
                    exact hspare s hs) i c hc]
              exact ih i c hc
            simp only [grayChargedStepV2, hslots, Bool.false_eq_true, ↓reduceIte, hgoal]
            split
            · split
              · exact key _ rfl
              · exact key _ rfl
            · exact key _ rfl
          · simpa [grayChargedStepV2, hslots, hgoal] using ih i c hc
      | done core hdone =>
          intro i c hc
          simpa [grayChargedStepV2] using ih i c hc

/-- **The source son bases of the displayed entries are capped** by
`dyadicScale e` at every time of the V2 run (the displayed slots are the
active slots, none on a done core). -/
theorem grayChargedRunStateV2_display_sonBase_le
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : c.val < grayChargedSourceCount a e) :
    grayTailSonBase
      (grayTailEntries
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)
        (if (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done then []
        else (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots)
        (grayChargedCurrentMoveV2 q L a e sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t))) i c ≤ dyadicScale e := by
  have hsourceCap := grayChargedSourceBaseCapV2_stateAt (q := q) (L := L) (a := a)
    (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm) t
  have hcurrent := grayChargedRunStateV2_advantageMove_coherent (t := t)
    ha hae hL hRung hsm
  have hactiveBase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage →
      ∀ s ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots,
        grayTailFrozenSonBase
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1) s.1 s.2.1 ≤
          dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
    intro hphase
    have h := grayChargedBlockV2_active_base_le_stateAt (n := n) q L a e sigma A sm t
    rw [← grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm t hphase] at h
    simpa [frozenV1OfV2] using h
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hsourceCap hcurrent hactiveBase hcert ⊢
  cases hcert with
  | advantage core hcore hsource hact =>
      simp only [grayChargedCurrentMoveV2, hact, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hempty : core.slots.isEmpty = true
      · have hnil : core.slots = [] := List.isEmpty_iff.mp hempty
        rw [ite_eq_left hempty, hnil]
        simp only [grayTailEntries, grayTailSlotEntries, List.length_nil, List.ofFn_zero,
          List.append_nil]
        exact hsourceCap i c hc
      · have hne : 1 ≤ core.slots.length := by
          cases hs : core.slots with
          | nil => simp [hs] at hempty
          | cons _ _ => simp
        have hcur := hcurrent rfl hact hne
        have hslotBase : grayTailSonBase
            (grayTailSlotEntries core.slots (grayBlockCurrentMoveV2 q L e sigma core)) i c ≤
            dyadicScale (grayCallDepth q e) :=
          grayChargedBlockCurrentSonBase_le_callScale (q := q) (L := L) (e := e)
            (r := core.frozen.length) (fun j hj => (hcur j hj).2.1)
            (fun i c => grayInAdvBlock_fibre_count_le hcore.shape.slots_nodup
              hcore.shape.slots_range i c) i c
        rw [ite_eq_right hempty, grayTailEntries, grayTailSonBase_append_globalEntries]
        by_cases hhas : GrayTailHasKey core.slots i c
        · obtain ⟨s, hs, hi, hc'⟩ := hhas
          have hfrozen : grayTailFrozenSonBase (core.frozen.map GrayTailRoundV2.toV1) i c ≤
              dyadicScale e - dyadicScale e / (6 * halfAmplification q) := by
            have h := hactiveBase rfl s hs
            rw [hi, hc'] at h
            exact h
          exact le_trans (add_le_add hfrozen hslotBase)
            (grayTail_callScale_add_threshold_le q e)
        · rw [grayTailSonBase_eq_zero_of_not_hasKey i c hhas, add_zero]
          exact hsourceCap i c hc
  | wait core hcore hsource hdone =>
      have hcur : grayChargedCurrentMoveV2 q L a e sigma
          { phase := .advantage, core := core } = [] := by
        simp [grayChargedCurrentMoveV2, hdone]
      rw [hcur, ite_eq_left hdone]
      simp only [grayTailEntries, grayTailSlotEntries, List.length_nil, List.ofFn_zero,
        List.append_nil]
      exact hsourceCap i c hc
  | spend pass core hspend =>
      have hempty : core.slots.isEmpty = false := hspend.slots_nonempty
      have hzero : grayTailSonBase
          (grayTailSlotEntries core.slots (grayBlockSpendMoveV2 q L a e pass sigma core))
          i c = 0 := by
        apply grayTailSonBase_eq_zero_of_no_match
        intro z hz
        rw [grayTailSlotEntries, List.mem_ofFn] at hz
        obtain ⟨j, rfl⟩ := hz
        right
        intro heq
        have hmem : core.slots.get j ∈ grayChargedSlotsForPassV2 q L a e pass core.frozen := by
          rw [← hspend.slots_eq]
          exact List.get_mem _ _
        have hge : grayChargedSourceCount a e ≤ (core.slots.get j).2.1.val :=
          grayBlockSpendSlotsV2_son_ge (by simpa [grayChargedSlotsForPassV2] using hmem)
        have hval : (core.slots.get j).2.1.val = c.val := congrArg Fin.val heq
        omega
      simp only [grayChargedCurrentMoveV2, hempty, hspend.done_false, Bool.false_eq_true,
        ↓reduceIte]
      rw [grayTailEntries, grayTailSonBase_append_globalEntries, hzero, add_zero]
      exact hsourceCap i c hc
  | done core hdone =>
      simp only [grayChargedCurrentMoveV2]
      rw [ite_eq_left hdone.done_true]
      simp only [grayTailEntries, grayTailSlotEntries, List.length_nil, List.ofFn_zero,
        List.append_nil]
      exact hsourceCap i c hc

/-! ### The root cap of the displayed entries -/

/-- A root whose source son bases are capped by `dyadicScale e` and whose
spare son bases vanish has charged root request at most `dyadicScale a`. -/
lemma grayChargedRootRequest_le_of_sonBase_bounds {n b q a e : ℕ} (hae : a ≤ e)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n)
    (hbase : ∀ c : Fin b, c.val < grayChargedSourceCount a e →
      grayTailSonBase entries i c ≤ dyadicScale e)
    (hspare : ∀ c : Fin b, grayChargedSourceCount a e ≤ c.val →
      grayTailSonBase entries i c = 0) :
    grayChargedRootRequest (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) entries i ≤ dyadicScale a := by
  have hson : ∀ c : Fin b,
      grayChargedSonRequest (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c ≤
        if c.val < grayChargedSourceCount a e then dyadicScale e else 0 := by
    intro c
    by_cases hc : c.val < grayChargedSourceCount a e
    · unfold grayChargedSonRequest grayTailSonRequest
      simp only [ite_eq_left hc]
      by_cases hlarge : grayChargedThreshold q e < grayTailSonBase entries i c
      · rw [ite_eq_left hlarge]
      · rw [ite_eq_right hlarge]
        exact hbase c hc
    · have hge : grayChargedSourceCount a e ≤ c.val := Nat.le_of_not_gt hc
      simp only [grayChargedSonRequest_spare i c hge, hspare c hge, ite_eq_right hc, le_refl]
  unfold grayChargedRootRequest
  calc
    (∑ c : Fin b, grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i c) ≤
        ∑ c : Fin b, if c.val < grayChargedSourceCount a e then dyadicScale e else 0 :=
      Finset.sum_le_sum fun c _ => hson c
    _ = ∑ c ∈ Finset.univ.filter
          (fun c : Fin b => c.val < grayChargedSourceCount a e), dyadicScale e := by
        rw [Finset.sum_filter]
    _ = ((Finset.univ.filter
          (fun c : Fin b => c.val < grayChargedSourceCount a e)).card : ℚ) *
          dyadicScale e := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (grayChargedSourceCount a e : ℚ) * dyadicScale e := by
        apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
        exact_mod_cast grayTail_source_fin_card_le b (grayChargedSourceCount a e)
    _ = dyadicScale a := grayChargedSource_mass hae

/-- The slot of an entry of the projected ledger is a frozen or a current
slot. -/
lemma grayChargedV2_entries_slot_mem {n b : ℕ} {frozen : List (GrayTailRoundV2 n b)}
    {slots : List (GrayTailSlot n b)} {current : FamilyClientMove}
    {z : GrayTailSlot n b × ClientMove}
    (hz : z ∈ grayTailEntries (frozen.map GrayTailRoundV2.toV1) slots current) :
    (∃ p ∈ frozen, z.1 ∈ p.slots) ∨ z.1 ∈ slots := by
  rw [grayTailEntries, List.mem_append] at hz
  rcases hz with hz | hz
  · rw [grayTailFrozenEntries, List.mem_flatMap] at hz
    obtain ⟨pV1, hpV1, hz⟩ := hz
    rw [List.mem_map] at hpV1
    obtain ⟨p, hp, rfl⟩ := hpV1
    rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    exact Or.inl ⟨p, hp, List.get_mem _ _⟩
  · rw [grayTailSlotEntries, List.mem_ofFn] at hz
    obtain ⟨j, rfl⟩ := hz
    exact Or.inr (List.get_mem _ _)

/-- **The V2 per-pass increment upper bound from the coherence cap** at the
pinned gap `e = a + 8 * L + 3` (written out in the statement): a spend block
whose per-root requests are capped at the pass anchor scale contributes at
most `α/8` to every root. -/
lemma grayBlockRootIncrementV2_spend_upper_of_cap {q L a n pass : ℕ}
    (hpass : pass < 8)
    (frozen : GrayTailFrozen n (grayTailBranch q L a (a + 8 * L + 3)))
    (slots : List (GrayTailSlot n (grayTailBranch q L a (a + 8 * L + 3))))
    (hslots : slots = grayBlockSpendSlotsV2
      (grayChargedSourceCount a (a + 8 * L + 3)) L pass
      (grayChargedThreshold q (a + 8 * L + 3)) (dyadicScale (a + 8 * L + 3))
      (dyadicScale a) frozen)
    (move : FamilyClientMove)
    (hcap : ∀ j < slots.length,
      getReq (familyClientMoveAt move j) [] ≤
        dyadicScale (grayChargedSpendEps a L (a + 8 * L + 3) pass))
    (i : Fin n) :
    grayChargedRootIncrement (grayTailSlotEntries slots move) i ≤ dyadicScale a / 8 := by
  subst hslots
  by_cases hi : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a (a + 8 * L + 3))
      (grayChargedThreshold q (a + 8 * L + 3)) (dyadicScale (a + 8 * L + 3))
      (dyadicScale a) frozen
  · set slots := grayBlockSpendSlotsV2 (grayChargedSourceCount a (a + 8 * L + 3)) L pass
      (grayChargedThreshold q (a + 8 * L + 3)) (dyadicScale (a + 8 * L + 3))
      (dyadicScale a) frozen with hslotsDef
    set rootslots := Finset.univ.filter
      (fun j : Fin slots.length => (slots.get j).1 = i) with hrootsDef
    have hcard : rootslots.card = graySpendMult L pass := by
      calc
        rootslots.card = (slots.filter fun s => decide (s.1 = i)).length := by
          simpa [rootslots, List.get_eq_getElem] using grayCharged_filter_index_card slots i
        _ = graySpendMult L pass := by
          rw [hslotsDef, grayBlockSpendSlotsV2_filter_root_length, ite_eq_left hi,
            grayBlockSpendPairs_length_pinned rfl hpass]
    have hsum : grayChargedRootIncrement (grayTailSlotEntries slots move) i =
        ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
      rw [grayChargedRootIncrement_slotEntries_eq_sum]
      dsimp [rootslots]
      rw [Finset.sum_filter]
    rw [hsum]
    calc
      (∑ j ∈ rootslots, getFamilyReq move j.val []) ≤
          ∑ _j ∈ rootslots,
            dyadicScale (grayChargedSpendEps a L (a + 8 * L + 3) pass) := by
        apply Finset.sum_le_sum
        intro j _
        exact hcap j.val j.isLt
      _ = (rootslots.card : ℚ) *
          dyadicScale (grayChargedSpendEps a L (a + 8 * L + 3) pass) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (graySpendMult L pass : ℚ) *
          dyadicScale (grayChargedSpendEps a L (a + 8 * L + 3) pass) := by
        rw [hcard]
      _ = dyadicScale a / 8 :=
        @graySpendBlockV2_alpha_mass q a L (a + 8 * L + 3) pass rfl hpass
  · rw [grayBlockRootIncrementV2_spend_eq_zero (q := q) (L := L) (a := a)
      (e := a + 8 * L + 3) (pass := pass) frozen move i hi]
    exact div_nonneg (dyadicScale_pos a).le (by norm_num)

/-- In the advantage phase (active or waiting), every spare son base of the
displayed entries vanishes: the source invariant confines the frozen slots
and the displayed slots to source sons. -/
lemma grayChargedV2_advantage_spare_sonBase_eq_zero {n b a e : ℕ}
    {core : GrayTailStateV2 n b}
    (hsource : GrayTailSourceInvariantV2 (grayChargedSourceCount a e) core)
    (current : FamilyClientMove) (i : Fin n) (c : Fin b)
    (hc : grayChargedSourceCount a e ≤ c.val) :
    grayTailSonBase
      (grayTailEntries (core.frozen.map GrayTailRoundV2.toV1)
        (if core.done then [] else core.slots) current) i c = 0 := by
  apply grayTailSonBase_eq_zero_of_no_match
  intro z hz
  right
  intro heq
  have hval : z.1.2.1.val = c.val := congrArg Fin.val heq
  have hlt : z.1.2.1.val < grayChargedSourceCount a e := by
    rcases grayChargedV2_entries_slot_mem hz with ⟨p, hp, hzp⟩ | hzs
    · exact hsource.frozen p hp z.1 hzp
    · by_cases hd : core.done = true
      · rw [ite_eq_left hd] at hzs
        simp at hzs
      · rw [ite_eq_right hd] at hzs
        exact hsource.current z.1 hzs
  omega

/-- **The root cap of the displayed entries** at the pinned gap
`L = grayFootprint q`, `e = a + 8 * L + 3` (both written out in the
statement): at every time of the V2 run, every charged root request of the
displayed entries is at most `dyadicScale a` (the displayed slots are the
active slots, none on a done core). -/
theorem grayChargedRunStateV2_display_root_cap
    {q a n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm)
    (i : Fin n) :
    grayChargedRootRequest (grayChargedSourceCount a (a + 8 * grayFootprint q + 3))
      (grayChargedThreshold q (a + 8 * grayFootprint q + 3))
      (dyadicScale (a + 8 * grayFootprint q + 3))
      (grayTailEntries
        ((grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.frozen.map
            GrayTailRoundV2.toV1)
        (if (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.done then []
        else (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.slots)
        (grayChargedCurrentMoveV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma
          (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
            q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t)))
        i ≤ dyadicScale a := by
  obtain ⟨L, hL⟩ : ∃ L, L = grayFootprint q := ⟨grayFootprint q, rfl⟩
  rw [← hL] at hsm ⊢
  set e := a + 8 * L + 3 with hpin
  have hae : a ≤ e := by rw [hpin]; omega
  have hinv := grayChargedRequestInvariantV2_stateAt (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hpin hae t
  have hbase := fun (c : Fin (grayTailBranch q L a e))
      (hc : c.val < grayChargedSourceCount a e) =>
    grayChargedRunStateV2_display_sonBase_le (t := t) ha hae hL hRung hsm i c hc
  have hcurSpend := fun (pass : ℕ)
      (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .spend pass) =>
    grayChargedRunStateV2_spendMove_coherent (t := t) hL hRung hsm pass hphase
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hinv hbase hcurSpend hcert ⊢
  cases hcert with
  | advantage core hcore hsource hact =>
      exact grayChargedRootRequest_le_of_sonBase_bounds hae _ i hbase
        (fun c hc => grayChargedV2_advantage_spare_sonBase_eq_zero hsource _ i c hc)
  | wait core hcore hsource hdone =>
      exact grayChargedRootRequest_le_of_sonBase_bounds hae _ i hbase
        (fun c hc => grayChargedV2_advantage_spare_sonBase_eq_zero hsource _ i c hc)
  | spend pass core hspend =>
      have hwindow : GrayChargedSpendWindow q a e pass
          (core.frozen.map GrayTailRoundV2.toV1) := by
        simpa [GrayChargedRequestInvariantV2] using hinv
      have hempty : core.slots.isEmpty = false := hspend.slots_nonempty
      have hcur := hcurSpend pass rfl
      have hslotsEq : core.slots = grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
          (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
          (core.frozen.map GrayTailRoundV2.toV1) := hspend.slots_eq
      simp only [grayChargedCurrentMoveV2, hempty, hspend.done_false, Bool.false_eq_true,
        ↓reduceIte]
      generalize hcurDef : grayBlockSpendMoveV2 q L a e pass sigma core = current at hcur ⊢
      have hspare : ∀ z ∈ grayTailSlotEntries core.slots current,
          grayChargedSourceCount a e ≤ z.1.2.1.val := by
        intro z hz
        rw [grayTailSlotEntries, List.mem_ofFn] at hz
        obtain ⟨j, rfl⟩ := hz
        have hmem : core.slots.get j ∈ grayChargedSlotsForPassV2 q L a e pass core.frozen := by
          rw [← hspend.slots_eq]
          exact List.get_mem _ _
        exact grayBlockSpendSlotsV2_son_ge (by simpa [grayChargedSlotsForPassV2] using hmem)
      have hsplit := grayChargedRootIncrement_append_spare
        (source := grayChargedSourceCount a e) (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries (core.frozen.map GrayTailRoundV2.toV1))
        (grayTailSlotEntries core.slots current) hspare i
      have hinc : grayChargedRootIncrement (grayTailSlotEntries core.slots current) i ≤
          dyadicScale a / 8 :=
        grayBlockRootIncrementV2_spend_upper_of_cap hspend.pass_lt
          (core.frozen.map GrayTailRoundV2.toV1) core.slots hslotsEq current
          (fun j hj => (hcur j hj).2.1) i
      rw [grayTailEntries, hsplit]
      by_cases hi : i ∈ grayChargedDeficientRoots (grayChargedSourceCount a e)
          (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
          (core.frozen.map GrayTailRoundV2.toV1)
      · have hfrozen : grayChargedFrozenRootRequest q a e
            (core.frozen.map GrayTailRoundV2.toV1) i < dyadicScale a / 2 :=
          (mem_grayChargedDeficientRoots_iff (grayChargedSourceCount a e)
            (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
            (core.frozen.map GrayTailRoundV2.toV1) i).1 hi
        change grayChargedFrozenRootRequest q a e (core.frozen.map GrayTailRoundV2.toV1) i +
            grayChargedRootIncrement (grayTailSlotEntries core.slots current) i ≤
          dyadicScale a
        linarith [dyadicScale_pos a]
      · have hzero : grayChargedRootIncrement (grayTailSlotEntries core.slots current) i = 0 := by
          rw [hslotsEq]
          exact grayBlockRootIncrementV2_spend_eq_zero (q := q) (L := L) (a := a) (e := e)
            (pass := pass) (core.frozen.map GrayTailRoundV2.toV1) current i hi
        change grayChargedFrozenRootRequest q a e (core.frozen.map GrayTailRoundV2.toV1) i +
            grayChargedRootIncrement (grayTailSlotEntries core.slots current) i ≤
          dyadicScale a
        rw [hzero, add_zero]
        exact (hwindow i).2.1
  | done core hdone =>
      have hwindow : GrayChargedDoneWindow q a e
          (core.frozen.map GrayTailRoundV2.toV1) := by
        simpa [GrayChargedRequestInvariantV2] using hinv
      simpa [grayChargedCurrentMoveV2, grayTailEntries, hdone.done_true,
        grayTailSlotEntries, grayChargedFrozenRootRequest] using (hwindow i).2

end Kolmogorov
