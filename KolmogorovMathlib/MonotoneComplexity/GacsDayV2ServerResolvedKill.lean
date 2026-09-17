import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendKillEarlier
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2FrozenSnap
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2DisjointAssembly

/-!
# v15: leaf 1's server-resolved class, anchoring-free

Every designated cell of every frozen SPEND round of the final V2 ledger is
prefix-incomparable with the exit-time plain reserve of every server-resolved
source son.  Chronology: a spend round comes after the advantage terminal
(terminal rounds have fine anchors), so its snapshot — the server move at the
last round frozen before it (`GrayChargedFrozenSnapV2`) — is taken at a time
`≥ advantageExitTime`, when the plain reserve's witness allocation is present;
the harvest kill (`GacsDayV2SpendKillEarlier`) does the rest.  No root-prefix
anchoring is used.
-/

namespace Kolmogorov

/-- Frozen server times are monotone along the ledger index. -/
lemma grayChargedRunStateV2_frozen_serverTime_mono {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (U : Nat) {i j : Nat}
    (hi : i < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length)
    (hj : j < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length)
    (hij : i <= j) :
    ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[i]'hi).serverTime <=
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[j]'hj).serverTime := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · have hcert := grayChargedRunStateV2_coreCertified (n := n) q L a e sigma A sm U
    exact le_of_lt (hcert.frozen_chrono i j hi hj h)
  · subst h
    exact le_rfl

/-- **The snapshot of a spend round of the final ledger is taken at a time
not before the advantage exit.** -/
lemma grayChargedReplayV2_spend_round_snapshot
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : replay.advantageExitTime + 1 <= U)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    ∃ t₁, replay.advantageDoneTime <= t₁ ∧
      p.unavailable = A ++ grayHarvest p.fineEnd p.slots n (sm t₁) := by
  classical
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨s0, hsOK, hsnap⟩ := grayChargedRunStateV2_frozenSnap q L a e sigma A sm U k hk
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
    rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hU
  obtain ⟨r, hconcat, hrtime⟩ := grayChargedReplayV2_terminal_frozen_eq_concat replay
  have hmpos : 1 <= replay.advantageTerminal.frozen.length := by
    rw [hconcat]
    simp
  -- a coarse round is not a terminal round
  have hmk : replay.advantageTerminal.frozen.length <= k := by
    by_contra hlt
    push Not at hlt
    have hpk' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[k]'hk =
        replay.advantageTerminal.frozen[k]'hlt := (hpre.getElem hlt).symm
    have hfine := grayChargedReplayV2_terminal_round_adv replay
      (List.getElem_mem hlt)
    rw [← hpk', hpk] at hfine
    exact hcoarse hfine
  have hk1 : k - 1 < (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length := by omega
  -- the last round frozen before `p` is index `k - 1`
  have htake : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.take k =
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen.take (k - 1) ++
        [(grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen[k - 1]'hk1] := by
    have h := List.take_succ_eq_append_getElem (i := k - 1) hk1
    rw [show k - 1 + 1 = k by omega] at h
    exact h
  have hprevMem : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen[k - 1]'hk1 ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen.take k := by
    rw [htake]
    exact List.mem_append_right _ List.mem_cons_self
  -- the exit round is the terminal's last round, at index `m - 1`
  have hm1 : replay.advantageTerminal.frozen.length - 1 <
      replay.advantageTerminal.frozen.length := by omega
  have hr_eq : replay.advantageTerminal.frozen[replay.advantageTerminal.frozen.length - 1]'hm1
      = r := by
    have hlast_r : replay.advantageTerminal.frozen.getLast? = some r := by
      rw [hconcat]
      exact List.getLast?_concat
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hm1] at hlast_r
    exact Option.some.inj hlast_r
  have hm1' : replay.advantageTerminal.frozen.length - 1 <
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen.length := by
    have := hpre.length_le
    omega
  have hr_run : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen[replay.advantageTerminal.frozen.length - 1]'hm1'
      = r := by
    rw [← hpre.getElem hm1]
    exact hr_eq
  have hexit : replay.advantageDoneTime <=
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[k - 1]'hk1).serverTime := by
    have hmono := grayChargedRunStateV2_frozen_serverTime_mono q L a e sigma A sm U
      hm1' hk1 (by omega)
    rw [hr_run, hrtime] at hmono
    exact hmono
  -- the snapshot is a server time after the predecessor round
  have hsne : s0 ≠ none := by
    intro hnone
    have htk := hsOK.1 hnone
    have hlen : ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen.take k).length = k :=
      List.length_take_of_le (le_of_lt hk)
    rw [htk] at hlen
    simp at hlen
    omega
  obtain ⟨tsnap, htsnap⟩ := Option.ne_none_iff_exists'.mp hsne
  have hord := (hsOK.2 tsnap htsnap).2 _ hprevMem
  refine ⟨tsnap, le_trans hexit hord, ?_⟩
  rw [htsnap] at hsnap
  simp only [grayHarvestSnapshot] at hsnap
  rw [hpk] at hsnap
  exact hsnap

/-- **Leaf 1, server-resolved class, anchoring-free**: the designated cells
of every frozen spend round of the final ledger avoid the exit-time plain
reserve of every server-resolved source son. -/
theorem grayChargedReplayV2_spendRound_cell_avoids_serverResolved_reserve
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hroom : a + 3 + L <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : replay.advantageExitTime + 1 <= U)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2ServerResolvedSources replay)
    {R : BitString}
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm replay.advantageDoneTime) [z.2.val] R)
    (w : Nat × BitString)
    (hw : w ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (w.2 <+: R ∨ R <+: w.2) := by
  classical
  obtain ⟨t₁, ht, hsnap⟩ :=
    grayChargedReplayV2_spend_round_snapshot replay hU hp hcoarse
  have hsrc : z.2.val < grayChargedSourceCount a e :=
    (Finset.mem_filter.mp hz).2.1
  exact grayChargedSpendRoundV2_cell_incomparable_of_earlier_reserve hsm hae hroom p hp
    hcoarse hsnap ht z.1.isLt z.2.isLt hsrc hR w hw

/-- The server-resolved class carries an exit-time plain reserve. -/
lemma grayChargedReplayV2_serverResolved_reserve
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2ServerResolvedSources replay) :
    ∃ R, IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm replay.advantageDoneTime) [z.2.val] R := by
  classical
  exact (getTailFamilyReserve_isSome_iff e (grayTailBranch q L a e) A n z.1.val
    (sm replay.advantageDoneTime) [z.2.val]).mp (Finset.mem_filter.mp hz).2.2.2

end Kolmogorov
