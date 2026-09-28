import KolmogorovMathlib.MonotoneComplexity.GacsDayV2DisjointAssembly
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AllReduced

/-!
# Native coarse support and the straddle kill (amendment G2/G3, abstract layer)

The provenance-side predicate the corrected design threads through the
native certificate: every designated cell has a comparable slot allocation
of length at most the round's anchor. Its two consequences are proved here:
the cell's region sits under the witness, and — combined with an anchored
reserve and the sibling separation of the witness list from the anchor —
the cell can never share a dyadic cone with the reserve. What remains for
G2 is only SUPPLYING the certificate from the controller's acceptance.
-/

namespace Kolmogorov

/-- There is a cell `d ∈ S` of length at most `anchor` which is comparable with `p.take anchor`: the
designated cell `p` has a slot allocation no finer than the round's anchor. -/
def NativeCoarseSupportV2 (anchor : Nat) (S : List BitString)
    (p : BitString) : Prop :=
  exists d, d ∈ S ∧ d.length <= anchor ∧
    (p.take anchor <+: d ∨ d <+: p.take anchor)

/-- Coarse support forgets to the ordinary membership witness clause. -/
lemma NativeCoarseSupportV2.to_comparable
    {anchor : Nat} {S : List BitString} {p : BitString}
    (h : NativeCoarseSupportV2 anchor S p) :
    exists d, d ∈ S ∧ (p.take anchor <+: d ∨ d <+: p.take anchor) := by
  obtain ⟨d, hd, -, hcmp⟩ := h
  exact ⟨d, hd, hcmp⟩

/-- **The region step**: a coarse-supported cell sits inside its witness's
cylinder. -/
lemma NativeCoarseSupportV2.cell_under_witness
    {anchor : Nat} {S : List BitString} {p : BitString}
    (h : NativeCoarseSupportV2 anchor S p) (hlen : anchor <= p.length) :
    exists d, d ∈ S ∧ d.length <= anchor ∧ d <+: p := by
  obtain ⟨d, hd, hdlen, hcmp⟩ := h
  refine ⟨d, hd, hdlen, ?_⟩
  rcases hcmp with h1 | h1
  · have hlen2 : (p.take anchor).length = anchor := by
      rw [List.length_take]
      omega
    have hle := h1.length_le
    have hEq : p.take anchor = d := h1.eq_of_length (by omega)
    rw [← hEq]
    exact List.take_prefix _ _
  · exact h1.trans (List.take_prefix _ _)

/-- **The straddle kill** (amendment G3, cell level): a coarse-supported
cell whose witness list is prefix-separated from an anchored reserve's
anchor can never share a dyadic cone with the reserve — in either
orientation, the witness and the anchor would become two comparable
prefixes of one string. -/
theorem grayChargedV2_coarse_cell_anchored_reserve_incomparable
    {anchor : Nat} {S : List BitString} {w R v : BitString}
    (hsupp : NativeCoarseSupportV2 anchor S w)
    (hlen : anchor <= w.length)
    (hvR : v <+: R)
    (hsep : forall d, d ∈ S -> ¬ (v <+: d ∨ d <+: v)) :
    ¬ (w <+: R ∨ R <+: w) := by
  obtain ⟨d, hd, -, hdw⟩ := hsupp.cell_under_witness hlen
  rintro (h | h)
  · -- `d <+: w <+: R` and `v <+: R`: two prefixes of `R`
    have hdR : d <+: R := hdw.trans h
    rcases List.prefix_or_prefix_of_prefix hvR hdR with h2 | h2
    · exact hsep d hd (Or.inl h2)
    · exact hsep d hd (Or.inr h2)
  · -- `v <+: R <+: w` and `d <+: w`: two prefixes of `w`
    have hvw : v <+: w := hvR.trans h
    rcases List.prefix_or_prefix_of_prefix hvw hdw with h2 | h2
    · exact hsep d hd (Or.inl h2)
    · exact hsep d hd (Or.inr h2)

/-- Regions under prefix-incomparable covers stay prefix-incomparable. -/
lemma grayChargedV2_incomparable_of_covers
    {v' d' v d : BitString}
    (hv : v' <+: v) (hd : d' <+: d)
    (hsep : ¬ (v' <+: d' ∨ d' <+: v')) :
    ¬ (v <+: d ∨ d <+: v) := by
  rintro (h | h)
  · have hv'd : v' <+: d := hv.trans h
    rcases List.prefix_or_prefix_of_prefix hv'd hd with h2 | h2
    · exact hsep (Or.inl h2)
    · exact hsep (Or.inr h2)
  · have hd'v : d' <+: v := hd.trans h
    rcases List.prefix_or_prefix_of_prefix hd'v hv with h2 | h2
    · exact hsep (Or.inr h2)
    · exact hsep (Or.inl h2)

/-- **The anchor/foreign-slot separation** (amendment G3's `hsep`
supplier): an allocated anchor at a source son node is prefix-incomparable
with every allocation of a foreign slot's local list, at any pair of
times — persist both to a common time, take the coherence covers, and
descend. -/
theorem grayChargedV2_anchor_foreign_slot_incomparable
    {n b L : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm)
    {i : Fin n} {c : Fin b} {tau : Nat} {v : BitString}
    (hv : v ∈ getFamilyAlloc (sm tau) i.val [c.val])
    (p : GrayTailRound n b) (j : Fin p.slots.length)
    (hne : (p.slots.get j).1 ≠ i ∨ (p.slots.get j).2.1 ≠ c)
    {d : BitString}
    (hd : d ∈ getFamilyAlloc
      (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime))
      j.val []) :
    ¬ (v <+: d ∨ d <+: v) := by
  classical
  set s := p.slots.get j with hs
  set M := max tau p.serverTime with hM
  have hdfam : d ∈ getFamilyAlloc (sm p.serverTime) s.1.val
      [s.2.1.val, s.2.2.val] := by
    rw [getFamilyAlloc_grayTailLocalServerMove
      p.slots (sm p.serverTime) j.val j.isLt [] (by simp)] at hd
    have hd' := (mem_truncAlloc.mp hd).1
    simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'
  obtain ⟨v1, hv1, hv1v⟩ := allocationSubset_mono_time
    (hsm.1 i.val i.isLt) (le_max_left tau p.serverTime) [c.val] v hv
  obtain ⟨d1, hd1, hd1d⟩ := allocationSubset_mono_time
    (hsm.1 s.1.val s.1.isLt) (le_max_right tau p.serverTime)
    [s.2.1.val, s.2.2.val] d hdfam
  by_cases htree : s.1 = i
  · -- same tree, different son: sibling coherence at the common time
    have hson : s.2.1 ≠ c := by
      rcases hne with h | h
      · exact absurd htree h
      · exact h
    have hcoh := (hsm.1 i.val i.isLt).1 M
    have hd1' : d1 ∈ getAlloc (familyServerMoveAt (sm M) i.val)
        ([s.2.1.val] ++ [s.2.2.val]) := by
      have := hd1
      rw [htree] at this
      exact this
    obtain ⟨b1, hb1, hb1d1⟩ := hcoh.1 [s.2.1.val] s.2.2 d1 hd1'
    have hsib := hcoh.2 ([] : GacsDayNode) c s.2.1
      (fun h => hson h.symm)
    have hv1' : v1 ∈ getAlloc (familyServerMoveAt (sm M) i.val)
        (([] : GacsDayNode) ++ [c.val]) := hv1
    have hb1' : b1 ∈ getAlloc (familyServerMoveAt (sm M) i.val)
        (([] : GacsDayNode) ++ [s.2.1.val]) := hb1
    have hsep := hsib v1 hv1' b1 hb1'
    exact grayChargedV2_incomparable_of_covers hv1v
      (hb1d1.trans hd1d) hsep
  · -- different trees: root disjointness at the common time
    have hroot := hsm.2.1 M s.1.val s.1.isLt i.val i.isLt
      (fun h => htree (Fin.ext h))
    have hcohI := (hsm.1 i.val i.isLt).1 M
    have hcohS := (hsm.1 s.1.val s.1.isLt).1 M
    obtain ⟨v0, hv0, hv0v1⟩ := allocationSubset_getAlloc_root hcohI
      [c.val] (by
        intro z hz
        simp only [List.mem_singleton] at hz
        subst hz
        exact c.isLt) v1 hv1
    obtain ⟨d0, hd0, hd0d1⟩ := allocationSubset_getAlloc_root hcohS
      [s.2.1.val, s.2.2.val] (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact s.2.1.isLt
        · exact s.2.2.isLt) d1 hd1
    have hsep := hroot d0 hd0 v0 hv0
    have hsep' : ¬ (v0 <+: d0 ∨ d0 <+: v0) := by
      rintro (h | h)
      · exact hsep (Or.inr h)
      · exact hsep (Or.inl h)
    exact grayChargedV2_incomparable_of_covers
      (hv0v1.trans hv1v) (hd0d1.trans hd1d) hsep'

/-- **G3 assembled for one spend round**: given the (future) coarse
certificate for the round's cells and an anchored reserve of a source son,
every cell of the round is prefix-incomparable with the reserve — spare
slots are foreign, the anchor separates, the coarse witness pins the
cell. Leaf 1's raised-class spend side reduces to supplying `hcoarse`. -/
theorem grayChargedV2_spendRound_straddle_killed_of_coarse
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hspare : forall s, s ∈ p.slots ->
      grayChargedSourceCount a e <= s.2.1.val)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)}
    (hcsrc : c.val < grayChargedSourceCount a e)
    {tau : Nat} {v R : BitString}
    (hv : v ∈ getFamilyAlloc (sm tau) i.val [c.val])
    (hvR : v <+: R)
    (hcoarse : forall z, z ∈ grayChargedRoundLocalChargeV2 hae p hp ->
      NativeCoarseSupportV2 p.blockAnchor
        (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L)
          p.slots (sm p.serverTime)) z.1 []) z.2)
    {z : Nat × BitString}
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  have hcells := grayChargedRoundLocalChargeV2_cells hae p hp z hz
  have hlt : z.1 < p.slots.length := hcells.1
  have hzlen : z.2.length = p.blockAnchor + L :=
    grayChargedRoundLocalChargeV2_cell_length hae p hp z hz
  have hne : (p.slots.get ⟨z.1, hlt⟩).1 ≠ i ∨
      (p.slots.get ⟨z.1, hlt⟩).2.1 ≠ c := by
    right
    intro hcontra
    have := hspare (p.slots.get ⟨z.1, hlt⟩) (List.get_mem _ _)
    rw [hcontra] at this
    omega
  have hsep : forall d, d ∈ getFamilyAlloc
      (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) z.1 [] ->
      ¬ (v <+: d ∨ d <+: v) := by
    intro d hd
    exact grayChargedV2_anchor_foreign_slot_incomparable (L := L) hsm hv
      p.toV1 ⟨z.1, hlt⟩ hne hd
  exact grayChargedV2_coarse_cell_anchored_reserve_incomparable
    (hcoarse z hz) (by omega) hvR hsep

/-- **Full disjointness for a raised son, conditional only on the coarse
certificates**: with the anchored serve-datum and per-spend-round
`NativeCoarseSupport`, the recursive ledger avoids the son's owner-aligned
complement — leaf 1's raised class reduces end-to-end to G2. -/
theorem grayChargedV2_raised_full_disjoint_of_coarse
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2RaisedSources replay)
    (hcoarse : forall i : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      replay.advantageTerminal.frozen.length <= i.val ->
      forall w, w ∈ grayChargedRoundLocalChargeV2 hae _
          (List.getElem_mem i.isLt) ->
        NativeCoarseSupportV2
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor
          (getFamilyAlloc (grayTailLocalServerMove
            (((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm
                (T + 1)).core.frozen[i.val]).blockAnchor + L)
            ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
            (sm ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm
                (T + 1)).core.frozen[i.val]).serverTime)) w.1 []) w.2) :
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
              Prod.snd) := by
  classical
  obtain ⟨tR, R, k, hdata, hanch⟩ :=
    grayChargedReplayV2_raised_anchored_datum hsm hnotpos replay z hz
  obtain ⟨v, hvmem, hvR⟩ := hanch.2
  have hk := grayChargedSonReserveDataV2_owner_lt hdata
  have hexitT : replay.advantageExitTime + 1 <= T + 1 := by
    have := replay.advantageExit_le
    omega
  have hdoneT : replay.advantageDoneTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  have hp' := grayChargedReplayV2_terminal_round_mem_late replay hdoneT
    (List.getElem_mem hk)
  have hz2 : z ∈ grayChargedRaisedSources
      (n := n) (b := grayTailBranch q L a e)
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (frozenV1OfV2 replay.advantageTerminal) := hz
  have hzsrc : z.2.val < grayChargedSourceCount a e :=
    (Finset.mem_filter.mp hz2).2.1
  refine ⟨tR, R, k, hk, hp', hdata, ?_⟩
  refine grayChargedV2_source_complement_disjoint hsm hae replay hU hdata
    hk hp' ?_
  intro i hlate w hw y hy
  obtain ⟨hspare, -⟩ :=
    grayChargedV2_late_position_spend_facts hae hpin replay i hlate
  rw [grayChargedTransportRound, List.mem_flatMap] at hw
  obtain ⟨l, hl, hw⟩ := hw
  rw [List.mem_ofFn] at hl
  obtain ⟨j, rfl⟩ := hl
  refine grayChargedV2_transported_cell_ne_complement_of_incomparable hae
    _ (List.getElem_mem i.isLt) hw hy ?_
  intro u huR
  exact grayChargedV2_spendRound_straddle_killed_of_coarse hsm hae
    (List.getElem_mem i.isLt) hspare hzsrc hvmem hvR
    (hcoarse i hlate)
    (mem_grayChargeAtRoot.mp huR).1

end Kolmogorov
