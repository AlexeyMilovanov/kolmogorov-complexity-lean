import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CoarseSupport

/-!
# The coarse-outcome layer (D3b, route B — non-breaking core)

The spend acceptance exposes a **coarse** witness (length ≤ `spendEps`) for
every designated cell, and progress holds because a served request of scale
`2^{-spendEps}` (or coarser) yields such a witness by `Serves`.  This module
builds the part of that argument which is independent of the controller:

* the mass→length bridge (`Serves` at a dyadic scale gives a short cell);
* coarse support from a served witness comparable with the cell prefix;
* the **strengthened spend outcome** as a named predicate, and the proof
  that it delivers `hcoarse` — isolating leaf 1's raised class to a single
  controller-level obligation (the acceptance/progress swap).
-/

namespace Kolmogorov

/-- **Mass → length**: serving a request of dyadic scale `k` is witnessed by
an allocation of length at most `k`. -/
lemma serves_dyadicScale_imp_coarse {a : Allocation} {k : Nat}
    (h : Serves a (dyadicScale k)) :
    exists c, c ∈ a ∧ c.length <= k := by
  obtain ⟨c, hc, hmass⟩ := h
  refine ⟨c, hc, ?_⟩
  by_contra hlen
  push Not at hlen
  have hcast : (((dyadicScale k : ℚ) : ℝ)) = (1 / 2 : ℝ) ^ k := by
    simp only [dyadicScale]
    push_cast
    ring
  rw [hcast] at hmass
  have hstrict : (1 / 2 : ℝ) ^ c.length < (1 / 2 : ℝ) ^ k :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlen
  linarith

/-- **Coarse support from a served witness**: if the cell's coarse prefix is
comparable with a served (short) allocation, native coarse support holds. -/
lemma nativeCoarseSupport_of_served {anchor : Nat} {S : List BitString}
    {p : BitString} {d : BitString}
    (hd : d ∈ S) (hlen : d.length <= anchor)
    (hcmp : p.take anchor <+: d ∨ d <+: p.take anchor) :
    NativeCoarseSupportV2 anchor S p :=
  ⟨d, hd, hlen, hcmp⟩

/-- Every designated cell of the local charge of a spend round of the run, that is of a frozen round
beyond the advantage terminal of `replay`, has `NativeCoarseSupportV2` at that round's block
anchor in the round's slot-local root allocations: a comparable allocated cell no finer than the
anchor. -/
def GrayChargedSpendCoarseOutcomeV2
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm t) : Prop :=
  forall (i : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.frozen.length),
    replay.advantageTerminal.frozen.length <= i.val ->
    forall w, w ∈ grayChargedRoundLocalChargeV2 hae _
        (List.getElem_mem i.isLt) ->
      NativeCoarseSupportV2
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + 1)).core.frozen[i.val]).blockAnchor
        (getFamilyAlloc (grayTailLocalServerMove
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1)).core.frozen[i.val]).blockAnchor + L)
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1)).core.frozen[i.val]).slots
          (sm ((grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1)).core.frozen[i.val]).serverTime))
          w.1 []) w.2

/-- **Leaf 1's raised class from the coarse outcome** (D3b assembled): the
strengthened spend outcome discharges the coarse hypothesis, so every
raised son's owner-aligned complement is disjoint from the recursive
ledger.  Combined with the unconditional server-resolved class, this closes
leaf-1 modulo the single named `GrayChargedSpendCoarseOutcomeV2`. -/
theorem grayChargedV2_raised_full_disjoint_of_outcome
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (houtcome : GrayChargedSpendCoarseOutcomeV2 hae replay)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay) :
    exists (tR : Nat) (R : BitString) (k : Nat)
      (hk : k < replay.advantageTerminal.frozen.length)
      (hp' : replay.advantageTerminal.frozen[k] ∈
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen),
      GrayChargedSonReserveDataV2 replay z tR R k ∧
      List.Disjoint
        ((grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd)
        ((grayChargedReserveComplementV2 z.1.val
          (e + grayTailNewLoss q L) R
          (grayChargedOwnerFibreV2 hae
            (replay.advantageTerminal.frozen[k]) hp' z)).map
              Prod.snd) :=
  grayChargedV2_raised_full_disjoint_of_coarse hsm hae hpin hnotpos replay
    hU z hz houtcome

end Kolmogorov
