import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Chase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Sources

/-!
# The mixed-phase positional chase at the pinned gap (Stage D3, completion)

Cross-round disjointness of designated cells over the WHOLE charged run —
advantage and spend rounds together — at the pinned gap `e = a + 8L + 3`.
The pinned schedule stacks every window below every earlier one
(`fineEnd(later) ≤ blockAnchor(earlier)`), and the slot geometry separates
the three round-pair kinds: advantage pairs by grandson block ranges,
advantage–spend by the source/spare split, spend–spend by the pass blocks.
The spend-pass strict monotonicity along the ledger is consumed as a
hypothesis (supplied by the wrapper certificate).
-/

namespace Kolmogorov

/-- **The pinned mixed schedule**: the later round's fine end is at most the
earlier round's anchor, for every phase pair (advantage–advantage by round
index, spend below every advantage, spend–spend by pass). -/
lemma grayChargedMixed_delta_le {q L a e : Nat}
    (hpin : e = a + 8 * L + 3)
    {pIdx rIdx : Nat}
    (pShape : (Nat ⊕ Nat)) (rShape : (Nat ⊕ Nat))
    (pAnchor rFine : Nat)
    (hpA : match pShape with
      | Sum.inl _ => pAnchor = grayTailRoundEps q L e pIdx
      | Sum.inr pass => pass < 8 ∧
          pAnchor = grayChargedSpendEps a L e pass)
    (hrF : match rShape with
      | Sum.inl _ => rFine = grayTailRoundDelta q L e rIdx
      | Sum.inr pass => pass < 8 ∧
          rFine = grayChargedSpendDelta a L e pass)
    (hidx : pIdx < rIdx)
    (hRCadv : forall rr, rShape = Sum.inl rr ->
      rIdx < grayChargedAdvantageRoundCount q)
    (hpassOrder : forall pp rp, pShape = Sum.inr pp -> rShape = Sum.inr rp ->
      pp < rp)
    (hadvFirst : forall pp, pShape = Sum.inr pp ->
      forall rr, rShape = Sum.inl rr -> False) :
    rFine <= pAnchor := by
  cases pShape with
  | inl pa =>
      cases rShape with
      | inl ra =>
          -- advantage–advantage: the descending fine schedule
          have hRC := hRCadv ra rfl
          simp only at hpA hrF
          rw [hpA, hrF]
          unfold grayTailRoundEps grayTailRoundDelta grayTailRoundEps
          have hRC8 : grayChargedAdvantageRoundCount q =
              grayTailRoundCount q - 8 := rfl
          have hco : (grayTailRoundCount q - 1 - rIdx) + 1 <=
              grayTailRoundCount q - 1 - pIdx := by omega
          calc grayCallDepth q e +
                (grayTailRoundCount q - 1 - rIdx) * L + L
              = grayCallDepth q e +
                ((grayTailRoundCount q - 1 - rIdx) + 1) * L := by ring
            _ <= grayCallDepth q e +
                (grayTailRoundCount q - 1 - pIdx) * L :=
              Nat.add_le_add_left (Nat.mul_le_mul_right L hco) _
      | inr rp =>
          -- advantage(earlier)–spend(later): spend windows sit below `e`
          simp only at hpA hrF
          obtain ⟨hrp, hrF⟩ := hrF
          rw [hpA, hrF]
          have hsd : grayChargedSpendDelta a L e rp <= e := by
            rw [grayChargedSpendDelta, hpin,
              grayChargedSpendEps_pinned_eq hrp]
            have h2 : (7 - rp) * L + (rp * L) = 7 * L := by
              rw [← Nat.add_mul]
              congr 1
              omega
            have hle : (7 - rp) * L <= 7 * L :=
              Nat.mul_le_mul_right L (by omega)
            omega
          refine le_trans hsd ?_
          unfold grayTailRoundEps
          have := grayCallDepth_ge q e
          omega
  | inr pp =>
      cases rShape with
      | inl ra => exact (hadvFirst pp rfl ra rfl).elim
      | inr rp =>
          simp only at hpA hrF
          obtain ⟨hpp, hpA⟩ := hpA
          obtain ⟨hrp, hrF⟩ := hrF
          have hplt : pp < rp := hpassOrder pp rp rfl rfl
          rw [hpA, hrF, grayChargedSpendDelta, hpin,
            grayChargedSpendEps_pinned_eq hpp,
            grayChargedSpendEps_pinned_eq hrp]
          have h2 : (7 - rp) * L + L <= (7 - pp) * L := by
            have : (7 - rp) + 1 <= 7 - pp := by omega
            calc (7 - rp) * L + L = ((7 - rp) + 1) * L := by ring
              _ <= (7 - pp) * L := Nat.mul_le_mul_right L this
          omega

/-- The call-depth bound of a spend anchor (below) and an advantage anchor
(above). -/
lemma grayChargedSpendEps_lt_callDepth {q L a e pass : Nat} (hae : a <= e) :
    grayChargedSpendEps a L e pass < grayCallDepth q e := by
  have hsp : grayChargedSpendEps a L e pass <= e + 3 := by
    unfold grayChargedSpendEps grayChargedSpendAlphaDepth
    exact max_le (by omega) (by omega)
  have hc5 : e + 5 <= grayCallDepth q e := by
    have h4sz : 2 ^ 2 <= 3 * q + 5 := by omega
    have := Nat.lt_size.mpr h4sz
    unfold grayCallDepth
    omega
  omega

/-- **The mixed round-pair chase over the V2 charged run** (pinned gap):
designated local cells of two distinct frozen rounds — any phase pair, with
the spend-pass order and adv-before-spend order as hypotheses — are
prefix-incomparable. -/
theorem grayChargedRunV2_roundPair_incomparable
    {q L a e n t t0 : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    {p r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hr : r ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hidx : p.roundIndex < r.roundIndex)
    (hts : p.serverTime <= t0)
    (hrUnavail : r.unavailable =
      A ++ grayHarvest r.fineEnd r.slots n (sm t0))
    (hspendPass : forall pp rp, pp < 8 -> rp < 8 ->
      p.blockAnchor = grayChargedSpendEps a L e pp ->
      r.blockAnchor = grayChargedSpendEps a L e rp ->
      pp < rp)
    (hadvFirst : ¬ grayCallDepth q e <= p.blockAnchor ->
      grayCallDepth q e <= r.blockAnchor -> False)
    {j j' : Nat} (hj : j < p.slots.length)
    {cu cv : BitString}
    (hcu : cu ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j []) p.unavailable)
    (hcv : cv ∈ newGrayCellsList r.blockAnchor r.fineEnd
      (getFamilyAlloc (grayTailLocalServerMove r.fineEnd r.slots
        (sm r.serverTime)) j' []) r.unavailable) :
    ¬ (cu <+: cv ∨ cv <+: cu) := by
  have hpv := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid p hp
  have hrv := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t).round_valid r hr
  have hrFine : r.fineEnd = r.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hr
  rcases hpv.2.2.2.2.2 with ⟨hpA, hpF, -, hpBlock, hpRC, hpSrc⟩ |
    ⟨pp, hpp, hpA, hpF, -, hpSlots, -⟩ <;>
  rcases hrv.2.2.2.2.2 with ⟨hrA, hrF, -, hrBlock, hrRC, hrSrc⟩ |
    ⟨rp, hrp, hrA, hrF, -, hrSlots, -⟩
  · -- advantage–advantage
    have hdelta_le : r.fineEnd <= p.blockAnchor :=
      grayChargedMixed_delta_le (q := q) (L := L) (a := a) (e := e)
        hpin (pIdx := p.roundIndex) (rIdx := r.roundIndex)
        (Sum.inl 0) (Sum.inl 0) p.blockAnchor r.fineEnd
        (by simpa using hpA) (by simpa using hrF) hidx
        (fun _ _ => hrRC)
        (fun _ _ h _ => by simp at h)
        (fun _ h => by simp at h)
    have hpairs : forall sl, sl ∈ p.slots -> forall sl2, sl2 ∈ r.slots ->
        (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2) := by
      intro sl hsl sl2 hsl2 heq
      have hpg := hpBlock sl hsl
      have hrg := hrBlock sl2 hsl2
      exact grayInAdvBlock_ne_of_round_ne hpg hrg (Nat.ne_of_lt hidx)
        (congrArg (fun z => z.2.val) heq)
    exact grayChargedMixed_chase_core hsm hts hdelta_le hpairs hrFine
      hrUnavail hj hcu hcv
  · -- advantage–spend
    have hdelta_le : r.fineEnd <= p.blockAnchor :=
      grayChargedMixed_delta_le (q := q) (L := L) (a := a) (e := e)
        hpin (pIdx := p.roundIndex) (rIdx := r.roundIndex)
        (Sum.inl 0) (Sum.inr rp) p.blockAnchor r.fineEnd
        (by simpa using hpA) (by simpa using ⟨hrp, hrF⟩) hidx
        (fun rr h => by simp at h)
        (fun _ _ h _ => by simp at h)
        (fun _ h => by simp at h)
    have hpairs : forall sl, sl ∈ p.slots -> forall sl2, sl2 ∈ r.slots ->
        (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2) := by
      intro sl hsl sl2 hsl2 heq
      have hlt := hpSrc sl hsl
      have hge : grayChargedSourceCount a e <= sl2.2.1.val :=
        grayBlockSpendPairs_first_ge (hrSlots sl2 hsl2)
      have h1 : sl.2.1.val = sl2.2.1.val :=
        congrArg (fun z => z.1.val) heq
      omega
    exact grayChargedMixed_chase_core hsm hts hdelta_le hpairs hrFine
      hrUnavail hj hcu hcv
  · -- spend–advantage: excluded
    exfalso
    apply hadvFirst
    · rw [hpA]
      exact not_le.mpr (grayChargedSpendEps_lt_callDepth hae)
    · rw [hrA]
      unfold grayTailRoundEps
      exact Nat.le_add_right _ _
  · -- spend–spend
    have hplt : pp < rp := hspendPass pp rp hpp hrp hpA hrA
    have hdelta_le : r.fineEnd <= p.blockAnchor :=
      grayChargedMixed_delta_le (q := q) (L := L) (a := a) (e := e)
        hpin (pIdx := p.roundIndex) (rIdx := r.roundIndex)
        (Sum.inr pp) (Sum.inr rp) p.blockAnchor r.fineEnd
        (by simpa using ⟨hpp, hpA⟩) (by simpa using ⟨hrp, hrF⟩) hidx
        (fun rr h => by simp at h)
        (fun pp2 rp2 h1 h2 => by
          have e1 : pp = pp2 := (Sum.inr.injEq _ _).mp h1
          have e2 : rp = rp2 := (Sum.inr.injEq _ _).mp h2
          omega)
        (fun _ _ _ h => by simp at h)
    have hpairs : forall sl, sl ∈ p.slots -> forall sl2, sl2 ∈ r.slots ->
        (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2) := by
      intro sl hsl sl2 hsl2 heq
      have hdisj := grayBlockSpendPairs_disjoint
        (b := grayTailBranch q L a e)
        (source := grayChargedSourceCount a e) (L := L) hplt
      rw [List.disjoint_iff_ne] at hdisj
      exact hdisj (sl.2.1, sl.2.2) (hpSlots sl hsl)
        (sl2.2.1, sl2.2.2) (hrSlots sl2 hsl2) heq
    exact grayChargedMixed_chase_core hsm hts hdelta_le hpairs hrFine
      hrUnavail hj hcu hcv

/-- **The certificate-driven mixed chase**: cross-round cell
incomparability over the whole V2 charged run at the pinned gap, with both
geometric inputs (pair disjointness and window stacking) read off the
wrapper certificate. -/
theorem grayChargedRunV2_cells_incomparable
    {q L a e n t t0 : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3)
    {p r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hr : r ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hidx : p.roundIndex < r.roundIndex)
    (hts : p.serverTime <= t0)
    (hrUnavail : r.unavailable =
      A ++ grayHarvest r.fineEnd r.slots n (sm t0))
    {j j' : Nat} (hj : j < p.slots.length)
    {cu cv : BitString}
    (hcu : cu ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j []) p.unavailable)
    (hcv : cv ∈ newGrayCellsList r.blockAnchor r.fineEnd
      (getFamilyAlloc (grayTailLocalServerMove r.fineEnd r.slots
        (sm r.serverTime)) j' []) r.unavailable) :
    ¬ (cu <+: cv ∨ cv <+: cu) := by
  have hcert := grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t
  exact grayChargedMixed_chase_core hsm hts
    (hcert.frozen_window_order hpin p hp r hr hidx)
    (hcert.frozen_cross_pairs p hp r hr hidx)
    (grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hr)
    hrUnavail hj hcu hcv

/-- **Cross-round disjointness of the transported charges** (D3 → D1): at
the pinned gap, transported cylinder blocks of two distinct frozen rounds
are disjoint at any common final depth. -/
theorem grayChargedRunV2_transport_disjoint
    {q L a e n t D : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    {p r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hr : r ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hidx : p.roundIndex < r.roundIndex)
    {slots slots2 : List (GrayTailSlot n (grayTailBranch q L a e))} :
    List.Disjoint
      ((grayChargedTransportRound D slots
        (grayChargedRoundLocalChargeV2 hae p hp)).map Prod.snd)
      ((grayChargedTransportRound D slots2
        (grayChargedRoundLocalChargeV2 hae r hr)).map Prod.snd) := by
  have hcert := grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm t
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  obtain ⟨jj, hjj, hrj⟩ := List.getElem_of_mem hr
  have hij : i < jj := by
    have h1 := hcert.frozen_index i hi
    have h2 := hcert.frozen_index jj hjj
    rw [hpi] at h1
    rw [hrj] at h2
    omega
  -- the snapshot of round jj is a server time after every earlier round
  obtain ⟨s, hsOK, hchainj⟩ := hcert.frozen_chain jj hjj
  have hsne : s ≠ none := by
    intro hnone
    have htake := hsOK.1 hnone
    have hlen : ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.take jj).length = jj :=
      List.length_take_of_le (le_of_lt hjj)
    rw [htake] at hlen
    simp at hlen
    omega
  obtain ⟨tsnap, htsnap⟩ := Option.ne_none_iff_exists'.mp hsne
  have hts : p.serverTime <= tsnap := by
    have hlen : i < ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.take jj).length := by
      rw [List.length_take_of_le (le_of_lt hjj)]
      exact hij
    have hmem : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.take jj := by
      have := List.getElem_mem hlen
      rw [List.getElem_take, hpi] at this
      exact this
    exact (hsOK.2 tsnap htsnap).2 _ hmem
  rw [htsnap] at hchainj
  simp only [grayHarvestSnapshot] at hchainj
  rw [hrj] at hchainj
  apply grayChargedTransportRound_disjoint_of_incomparable_bases
  intro u hu v hv
  have hcu := (grayChargedRoundLocalChargeV2_cells hae p hp u hu).2
  have hcv := (grayChargedRoundLocalChargeV2_cells hae r hr v hv).2
  have hrFine : r.fineEnd = r.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hr
  have hcv' : v.2 ∈ newGrayCellsList r.blockAnchor r.fineEnd
      (getFamilyAlloc (grayTailLocalServerMove r.fineEnd r.slots
        (sm r.serverTime)) v.1 []) r.unavailable := by
    rw [hrFine]
    exact hcv
  exact grayChargedRunV2_cells_incomparable hsm hpin hp hr hidx hts
    hchainj (grayChargedRoundLocalChargeV2_cells hae p hp u hu).1 hcu hcv'

end Kolmogorov
