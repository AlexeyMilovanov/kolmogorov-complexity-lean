import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFibre

/-!
# Leaf C of the tail frontier, decomposed

`grayTail_selected_round_accounting` (Leaf C) records two facts about the
frozen rounds of one terminal snapshot and one selected outer subfamily `I`:

* the **selected-request identity** -- summing the signed selected requests of
  all rounds reproduces `2 * Gamma(I) - Gamma(*)` for the accumulated son
  requests;
* the **per-round credit** -- each round pays for its own clamped signed
  request *after* the owner-charged sons have been deleted from the selected
  side.

The decomposition is

```text
C0  grayTail_selectedRequest_eq_fibreSum   slot sums = son sums      (proved,
                                           in GacsDayLadderTailFibre)
C1  grayTail_roundSigned_sum_eq            selected-request identity (proved)
C2  grayTail_chargedKeep_signed_eq         doubled-owner deletion    (proved)
C3  grayTail_chargedKeep_positivePart      per-round credit          (proved)
```

`C2` is where the factor `2` of `grayTailOwnerCharge` comes from and is kept:
`grayTailRoundSigned I p = 2 * selected - total`, so deleting a selected son of
increment `x` from the *selected* side alone removes `2 * x` from the signed
expression while leaving the total untouched.  `C3` is then an immediate
instance of the already proved `grayTailRound_selected_positivePart`.

Both `C1` and `C2` are now proved from the fibre identity `C0`: every request
appearing in them is first rewritten as a sum over the sons `(i, c)` of the
round, after which the identities are finite-sum algebra.  `C2` additionally
uses `GrayTailTerminalData.round_index_eq`, which says that the recorded round
index of a frozen round is its position in the frozen list, so that the owner
charge of round `p.roundIndex` really refers to `p`.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ### C1: the selected-request identity -/

/-- **Child C1 (proved).**  Summing the signed selected requests of all frozen
rounds reproduces the signed accumulated son requests of the subfamily.

Each round's selected request is the sum of the increments its slots carry
(`grayTail_selectedRequest_eq_fibreSum`), and the accumulated request
`grayTailGamma` of a root is by definition the sum of those increments over all
frozen rounds; the identity is the exchange of the two finite sums. -/
theorem grayTail_roundSigned_sum_eq_of_frozenSonBase
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hgamma : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen i c =
        ((grayTailRunState q L a e n sigma A sm T).frozen.map fun p =>
          grayTailSonBase (grayTailSlotEntries p.slots p.move) i c).sum)
    (I : List ℕ) :
    (((grayTailRunState q L a e n sigma A sm T).frozen.map
        (grayTailRoundSigned I)).sum) =
      2 * ∑ i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ I,
            grayTailGamma (grayTailRunState q L a e n sigma A sm T).frozen i -
        ∑ i : Fin n, grayTailGamma (grayTailRunState q L a e n sigma A sm T).frozen i := by
  classical
  -- the selected request of a round, as a sum over the selected sons
  have hsel : ∀ p : GrayTailRound n (grayTailBranch q L a e),
      totalRootRequestOnList (grayTailSelectedIndices (grayTailSelectKeep I) p) p.move =
        ∑ z ∈ Finset.univ.filter
            (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true),
          grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 :=
    fun p => grayTail_selectedRequest_eq_fibreSum p (fun i _ => decide (i.val ∈ I))
  -- the total request of a round, as a sum over all sons
  have htot : ∀ p : GrayTailRound n (grayTailBranch q L a e),
      totalRootRequest p.slots.length p.move =
        ∑ z : Fin n × Fin (grayTailBranch q L a e),
          grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 :=
    fun p => grayTail_totalRootRequest_eq_fibreSum p
  have hsigned :
      ((grayTailRunState q L a e n sigma A sm T).frozen.map (grayTailRoundSigned I)).sum =
      2 * ((grayTailRunState q L a e n sigma A sm T).frozen.map fun p =>
            ∑ z ∈ Finset.univ.filter
                (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true),
              grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2).sum -
        ((grayTailRunState q L a e n sigma A sm T).frozen.map fun p =>
          ∑ z : Fin n × Fin (grayTailBranch q L a e),
            grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2).sum := by
    rw [← grayTail_list_map_signed_sum]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro p _
    rw [grayTailRoundSigned, hsel p, htot p]
  rw [hsigned, grayTail_list_sum_map_finsetSum, grayTail_list_sum_map_finsetSum]
  -- each son's total increment is its accumulated request
  have hfrozen : ∀ z : Fin n × Fin (grayTailBranch q L a e),
      ((grayTailRunState q L a e n sigma A sm T).frozen.map fun p =>
          grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2).sum =
        grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen z.1 z.2 :=
    fun z => (hgamma z.1 z.2).symm
  simp only [hfrozen]
  -- regroup the son sums by root
  have hall : ∑ z : Fin n × Fin (grayTailBranch q L a e),
        grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen z.1 z.2 =
      ∑ i : Fin n, grayTailGamma (grayTailRunState q L a e n sigma A sm T).frozen i := by
    simp [grayTailGamma, Fintype.sum_prod_type]
  have hfil : (Finset.univ.filter
        (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true)) =
      (Finset.univ.filter fun i : Fin n => i.val ∈ I) ×ˢ
        (Finset.univ : Finset (Fin (grayTailBranch q L a e))) := by
    ext z
    simp [Finset.mem_product]
  have hselected :
      ∑ z ∈ Finset.univ.filter
          (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true),
          grayTailFrozenSonBase (grayTailRunState q L a e n sigma A sm T).frozen z.1 z.2 =
        ∑ i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ I,
          grayTailGamma (grayTailRunState q L a e n sigma A sm T).frozen i := by
    rw [hfil, Finset.sum_product]
    rfl
  rw [hall, hselected]

/-- The terminal-data wrapper used by Leaf C. -/
theorem grayTail_roundSigned_sum_eq
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (_hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (I : List ℕ) :
    (((grayTailRunState q L a e n sigma A sm T).frozen.map
        (grayTailRoundSigned I)).sum) =
      2 * ∑ i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ I,
            grayTailGamma (grayTailRunState q L a e n sigma A sm T).frozen i -
        ∑ i : Fin n, grayTailGamma
          (grayTailRunState q L a e n sigma A sm T).frozen i :=
  grayTail_roundSigned_sum_eq_of_frozenSonBase
    (fun i c => grayTail_frozenSonBase_eq_sum_rounds
      (grayTailRunState q L a e n sigma A sm T).frozen i c)
    I


/-! ### C2: deleting the owner-charged sons doubles their increment -/

/-- **Child C2 (proved).**  Removing from the *selected* side of one frozen
round exactly the selected sons it owns changes the signed selected request by
twice their owner-round increments, that is, by `grayTailOwnerCharge`.

The retained slots are selected by a predicate on the son `(i, c)` alone, so
the fibre identity turns both sides into sums over sons; the charged predicate
retains exactly the selected sons minus the ones this round owns, and
`GrayTailTerminalData.round_index_eq` identifies the round sitting at position
`p.roundIndex` with `p` itself. -/
theorem grayTail_chargedKeep_signed_eq
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (I : List ℕ) (p : GrayTailRound n (grayTailBranch q L a e))
    (hp : p ∈ (grayTailRunState q L a e n sigma A sm T).frozen) :
    2 * totalRootRequestOnList
        (grayTailSelectedIndices
          (grayTailChargedKeep (grayTailRunState q L a e n sigma A sm T).frozen
            (grayTailRunState q L a e n sigma A sm T).slots
            (2 ^ (e - a)) I p.roundIndex) p) p.move -
      totalRootRequest p.slots.length p.move =
    grayTailRoundSigned I p -
      grayTailOwnerCharge (grayTailRunState q L a e n sigma A sm T).frozen
        (grayTailRunState q L a e n sigma A sm T).slots
        (2 ^ (e - a)) I p.roundIndex := by
  classical
  -- the frozen round recorded at position `p.roundIndex` is `p` itself
  have hgetD :
      (grayTailRunState q L a e n sigma A sm T).frozen.getD p.roundIndex default = p := by
    obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
    have hidx := hdata.round_index_eq k hk
    simp only [List.get_eq_getElem, hkp] at hidx
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hkp]
    rfl
  set st := grayTailRunState q L a e n sigma A sm T with hst
  set used := 2 ^ (e - a) with hused
  set r := p.roundIndex with hr
  -- both selected requests as son sums
  set x : Fin n × Fin (grayTailBranch q L a e) → ℚ := fun z =>
    grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 with hx
  have hcharged :
      totalRootRequestOnList
        (grayTailSelectedIndices (grayTailChargedKeep st.frozen st.slots used I r) p) p.move =
      ∑ z ∈ Finset.univ.filter (fun z : Fin n × Fin (grayTailBranch q L a e) =>
        (decide (z.1.val ∈ I) &&
          !decide (z.2.val < used ∧ ¬ GrayTailHasSon st.slots z.1 z.2 ∧
            grayTailOwnerIndex st.frozen z.1 z.2 = r)) = true), x z :=
    grayTail_selectedRequest_eq_fibreSum p
      (fun i c => decide (i.val ∈ I) &&
        !decide (c.val < used ∧ ¬ GrayTailHasSon st.slots i c ∧
          grayTailOwnerIndex st.frozen i c = r))
  have hselect :
      totalRootRequestOnList (grayTailSelectedIndices (grayTailSelectKeep I) p) p.move =
      ∑ z ∈ Finset.univ.filter
        (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true), x z :=
    grayTail_selectedRequest_eq_fibreSum p (fun i _ => decide (i.val ∈ I))
  -- the charged sons are the selected ones minus the sons this round owns
  set D : Finset (Fin n × Fin (grayTailBranch q L a e)) :=
    (grayTailSelectedInactive st.slots used I).filter
      (fun z => grayTailOwnerIndex st.frozen z.1 z.2 = r) with hD
  have hsplit : (Finset.univ.filter (fun z : Fin n × Fin (grayTailBranch q L a e) =>
        (decide (z.1.val ∈ I) &&
          !decide (z.2.val < used ∧ ¬ GrayTailHasSon st.slots z.1 z.2 ∧
            grayTailOwnerIndex st.frozen z.1 z.2 = r)) = true))
      = (Finset.univ.filter
          (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true)) \ D := by
    ext z
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      grayTailSelectedInactive, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    tauto
  have hsub : D ⊆ Finset.univ.filter
      (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true) := by
    intro z hz
    simp only [hD, Finset.mem_filter, grayTailSelectedInactive, Finset.mem_univ,
      true_and, decide_eq_true_eq] at hz ⊢
    exact hz.1.1
  have hdiff : ∑ z ∈ (Finset.univ.filter
        (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true)) \ D, x z =
      (∑ z ∈ Finset.univ.filter
          (fun z : Fin n × Fin (grayTailBranch q L a e) => decide (z.1.val ∈ I) = true), x z)
        - ∑ z ∈ D, x z := Finset.sum_sdiff_eq_sub hsub
  -- the owner charge of this round is twice the deleted increment
  have howner : grayTailOwnerCharge st.frozen st.slots used I r = 2 * ∑ z ∈ D, x z := by
    rw [grayTailOwnerCharge, hgetD]
  rw [grayTailRoundSigned, hcharged, hsplit, hdiff, ← hselect, howner]
  ring

/-! ### C3: the per-round credit -/

/-- **Child C3 (proved).**  Each frozen round pays for its own owner-charged
clamped signed request.

This is `grayTailRound_selected_positivePart` for the charged keep predicate,
rewritten along the deletion identity `C2`. -/
theorem grayTail_chargedKeep_positivePart
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (I : List ℕ) (p : GrayTailRound n (grayTailBranch q L a e))
    (hp : p ∈ (grayTailRunState q L a e n sigma A sm T).frozen) :
    max 0 (halfAmplification q *
        (grayTailRoundSigned I p -
          grayTailOwnerCharge (grayTailRunState q L a e n sigma A sm T).frozen
            (grayTailRunState q L a e n sigma A sm T).slots
            (2 ^ (e - a)) I p.roundIndex)) ≤
      grayMassOfCount (p.epsDepth + L)
        (newGrayCount p.epsDepth (p.epsDepth + L)
          (familyAllocatedOnList
            (grayTailSelectedIndices
              (grayTailChargedKeep (grayTailRunState q L a e n sigma A sm T).frozen
                (grayTailRunState q L a e n sigma A sm T).slots
                (2 ^ (e - a)) I p.roundIndex) p)
            (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime)))
          p.unavailable) := by
  have hcred := grayTailRound_selected_positivePart hdata.certified hp
    (grayTailChargedKeep (grayTailRunState q L a e n sigma A sm T).frozen
      (grayTailRunState q L a e n sigma A sm T).slots
      (2 ^ (e - a)) I p.roundIndex)
  rwa [grayTail_chargedKeep_signed_eq hdata I p hp] at hcred

/-! ### Leaf C, assembled from its children -/

/-- **Leaf C (parent).**  Round and owner accounting for the actual frozen
rounds: the selected-request identity of `C1` together with the per-round
credit of `C3`. -/
theorem grayTail_selected_round_accounting
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (_ha : 1 ≤ a) (_hae : a ≤ e)
    (_hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hdata : GrayTailTerminalData q L a e n sigma A sm T)
    (I : List ℕ) (_hI : I ∈ (List.range n).sublists) :
    GrayTailSelectedRoundAccounting q L a e n sigma A sm T I :=
  ⟨grayTail_roundSigned_sum_eq hdata I,
    fun p hp => grayTail_chargedKeep_positivePart hdata I p hp⟩

end Kolmogorov
