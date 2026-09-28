import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RoundPositive
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2DoneOrNonempty
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2GoalCoarsen
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChildBranching
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvantageExit

/-!
# O3 closed: the block advantage phase exits, from the pinned rung

The V2 analogue of `grayChargedTailRound_gameSpec` /
`grayChargedTail_active_round_dichotomy` /
`grayChargedTail_eventually_terminal_or_positive` on the strict block
controller, consuming the **pinned** rung of the child stage
(`PinnedChargedRung 4 q sigma`, blueprint A4/C2):

* every active advantage round is a legal play of the child rung's game at
  the block anchor `ε_r` (gap `graySpendSpan q`, export `ε_r + fp q = δ_r`
  at the pinned per-round budget `L = fp q`), on the outer tree by the
  child-to-parent branching lemma;
* the rung's charged goal is certified at the child's anchor `ε_r` (v15.1
  A2), which is the block goal at the block anchor verbatim, so the round
  freezes at the first accepted exchange; otherwise the sub-game's unserved
  positive request transfers to the outer V2 client;
* a budget induction over the certified round bound reaches a terminal tail
  state, which is `done` (`grayChargedBlockV2_done_of_terminal`); the phase
  has then left, or the run is in the raised-service wait, which exits by the
  service horizon (`grayChargedV2_wait_exits`) — `GrayChargedAdvantageLeavesV2`.
-/

namespace Kolmogorov

/-- **The pinned rung supplies the game specification of every active V2
advantage round**, on the outer tree. -/
theorem grayChargedBlockRound_gameSpecV2
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {st : GrayTailStateV2 n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    ChargedGrayFamilyGameSpec 4 (halfAmplification q)
      (dyadicScale (grayTailRoundEps q L e st.frozen.length))
      ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e st.frozen.length))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      (2 * q) (grayTailBranch q L a e) st.slots.length st.unavailable
      (grayBlockRoundStrategyV2 q L e sigma st) := by
  have he1 : 1 <= e := le_trans ha hae
  have hcall1 : 1 <= grayCallDepth q e :=
    le_trans he1 (le_grayCallDepth q e)
  have hEps1 : 1 <= grayTailRoundEps q L e st.frozen.length :=
    le_trans hcall1 (grayTailRoundEps_lower q L e st.frozen.length)
  have hslots : 1 <= st.slots.length := by
    cases hs : st.slots with
    | nil => simp [hs] at hactive
    | cons _ _ => simp
  have hbase := hRung (grayTailRoundEps q L e st.frozen.length) hEps1
    st.slots.length st.unavailable hslots
  have hspan : forall x : Nat,
      x + 8 * grayFootprint (q - 1) + 3 = x + graySpendSpan q := by
    intro x
    unfold graySpendSpan
    omega
  have hbranch :
      ladderBranching (grayTailBaseBranch (q - 1) (grayFootprint (q - 1)))
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundEps q L e st.frozen.length +
            8 * grayFootprint (q - 1) + 3) <=
        grayTailBranch q L a e := by
    rw [hspan]
    have h1 := grayChildBranching_le_baseBranch (q := q) (L := L)
      (a' := grayTailRoundEps q L e st.frozen.length)
      (by rw [hL]; exact grayFootprint_pred_le q)
    have h2 : grayTailBaseBranch q L <= grayTailBranch q L a e :=
      le_max_right _ _
    exact le_trans h1 h2
  have hspec := hbase.mono_branching hbranch
  rw [hspan] at hspec
  subst hL
  unfold grayTailRoundDelta grayBlockRoundStrategyV2
  exact hspec

/-- **The active-round dichotomy of the V2 block controller**: from a round
start in the advantage phase, either the outer V2 client wins the positive
game, or the round freezes (one more frozen round at a fresh round start),
with the tail not done in between. -/
theorem grayChargedBlockV2_active_round_dichotomy
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailStateV2 n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      ∃ u, t < u ∧
        (∀ v, t <= v -> v < u ->
          (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm v).done = false) ∧
        (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).frozen.length = base.frozen.length + 1 ∧
          (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).roundStart = u ∧
          (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).history = ([], []) := by
  have hcert := grayChargedBlockTailCertifiedV2_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  rw [← hbase] at hcert
  have hspec := grayChargedBlockRound_gameSpecV2 (st := base) ha hae hL hRung hactive
  let localServer := grayBlockFutureServerV2 q L e base sm
  have hlocal : familyServerPlayLegal base.slots.length
      (grayTailBranch q L a e) base.unavailable localServer :=
    grayChargedBlockTailFutureServerV2_legal hcert hsm
  rcases hspec.wins_charged localServer hlocal with hwin | hgray
  · by_cases hg : ∃ T, grayChargedBlockRoundGoalBV2 q L e sigma base sm T = true
    · exact Or.inr (grayChargedBlockV2_freezes_of_round_gray
        base hbase hstart hactive hg)
    · exact Or.inl (grayChargedBlockV2_round_positive_of_not_gray
        hsm hbase hstart hactive hphase
        (hspec.weak.minimum_request localServer hlocal) hwin hg)
  · have hgray' : ∃ T, familyChargedGrayGoalAtB 4 (halfAmplification q)
        (dyadicScale (grayTailRoundEps q L e base.frozen.length))
        ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e base.frozen.length))
        (grayTailRoundEps q L e base.frozen.length)
        (grayTailRoundDelta q L e base.frozen.length)
        base.slots.length base.unavailable
        (playClientFamily base.unavailable base.slots.length
          (grayBlockRoundStrategyV2 q L e sigma base) localServer T)
        (localServer T) = true := hgray
    obtain ⟨T, hT⟩ := hgray'
    have hT' : grayChargedBlockRoundGoalBV2 q L e sigma base sm T = true := by
      unfold grayChargedBlockRoundGoalBV2 grayChargedBlockGoalAtB
      exact hT
    exact Or.inr (grayChargedBlockV2_freezes_of_round_gray
      base hbase hstart hactive ⟨T, hT'⟩)

/-- **Budget induction**: from a round start in the advantage phase, the
outer V2 client wins the positive game or the strict tail reaches a terminal
state. -/
theorem grayChargedBlockV2_eventually_terminal_or_positive
    {q L a e n t fuel : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailStateV2 n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hbudget : grayChargedAdvantageRoundCount q <= base.frozen.length + fuel) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      ∃ u, t <= u ∧
        ((grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).done ||
          (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).slots.isEmpty) = true := by
  induction fuel generalizing t base with
  | zero =>
      have hcount : grayChargedAdvantageRoundCount q <= base.frozen.length := by
        omega
      have hcert := grayChargedBlockTailCertifiedV2_stateAt
        (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
      rw [← hbase] at hcert
      have hdone : base.done = true := by
        by_contra h
        have hlt := hcert.frozen_bound.2 (Bool.eq_false_of_not_eq_true h)
        omega
      exact Or.inr ⟨t, le_rfl, by rw [← hbase]; simp [hdone]⟩
  | succ fuel ih =>
      by_cases hterminal : (base.done || base.slots.isEmpty) = true
      · exact Or.inr ⟨t, le_rfl, by simpa [hbase] using hterminal⟩
      · rcases grayChargedBlockV2_active_round_dichotomy ha hae hL hRung hsm
            hbase hstart hterminal hphase with hwin | hfreeze
        · exact Or.inl hwin
        · rcases hfreeze with ⟨u, htu, hbefore, hlen, hstart', _hhistory⟩
          by_cases hdoneU : (grayChargedBlockTailStateAtV2 (n := n)
              (b := grayTailBranch q L a e) q L a e sigma A sm u).done = true
          · exact Or.inr ⟨u, le_of_lt htu, by simp [hdoneU]⟩
          · have hdoneU' : (grayChargedBlockTailStateAtV2 (n := n)
                (b := grayTailBranch q L a e) q L a e sigma A sm u).done = false := by
              simpa using hdoneU
            have hphaseU : (grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e) q L a e sigma A sm u).phase =
                  .advantage :=
              grayChargedRunStateV2_phase_advantage_of_le hphase (le_of_lt htu)
                (fun v hv1 hv2 => by
                  rcases Nat.lt_or_eq_of_le hv2 with hlt | heq
                  · exact hbefore v hv1 hlt
                  · rw [heq]
                    exact hdoneU')
            have hbudget' : grayChargedAdvantageRoundCount q <=
                (grayChargedBlockTailStateAtV2 (n := n)
                  (b := grayTailBranch q L a e)
                  q L a e sigma A sm u).frozen.length + fuel := by
              rw [hlen]
              omega
            rcases ih (t := u) rfl hstart' hphaseU hbudget' with hwin | ⟨v, huv, hv⟩
            · exact Or.inl hwin
            · exact Or.inr ⟨v, le_trans (le_of_lt htu) huv, hv⟩

/-- **O3 closed from the pinned rung**: the V2 advantage phase is eventually
left, or the outer client wins the positive game. -/
theorem grayChargedV2_advantageLeaves_of_rung
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e) (hn : 1 <= n) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    GrayChargedAdvantageLeavesV2 q L a e n sigma A sm := by
  have h0 : grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm 0 =
      grayChargedBlockTailInitialStateV2 n (grayTailBranch q L a e) a e q L A := by
    simp [grayChargedBlockTailStateAtV2, grayTailServerPrefix,
      grayChargedBlockTailFoldV2]
  have hstart0 : (grayChargedBlockTailInitialStateV2 n
      (grayTailBranch q L a e) a e q L A).roundStart = 0 := rfl
  have hphase0 : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm 0).phase = .advantage := by
    simp [grayChargedRunStateV2, grayChargedFoldV2, grayChargedInitialStateV2,
      grayTailServerPrefix]
  have hbudget0 : grayChargedAdvantageRoundCount q <=
      (grayChargedBlockTailInitialStateV2 n
        (grayTailBranch q L a e) a e q L A).frozen.length +
          grayChargedAdvantageRoundCount q := by
    simp [grayChargedBlockTailInitialStateV2]
  rcases grayChargedBlockV2_eventually_terminal_or_positive
      (fuel := grayChargedAdvantageRoundCount q)
      ha hae hL hRung hsm (by rw [← h0]) hstart0 hphase0 hbudget0 with
    hwin | ⟨u, _hu, hterminal⟩
  · exact Or.inl hwin
  · -- the terminal is done: either the phase already left, or the run is in
    -- the raised-service wait, which exits by the service horizon
    by_cases hphaseU : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase = .advantage
    · have hdoneU := grayChargedBlockV2_done_of_terminal hn hterminal
      have hcoreU := grayChargedRunStateV2_core_eq_tailStateAt
        q L a e sigma A sm u hphaseU
      have hdone' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).core.done = true := by
        rw [hcoreU]
        exact hdoneU
      rcases grayChargedV2_wait_exits hsm hphaseU hdone' with hwin | ⟨v, -, hv⟩
      · exact Or.inl hwin
      · exact Or.inr ⟨v, hv⟩
    · exact Or.inr ⟨u, hphaseU⟩

end Kolmogorov
