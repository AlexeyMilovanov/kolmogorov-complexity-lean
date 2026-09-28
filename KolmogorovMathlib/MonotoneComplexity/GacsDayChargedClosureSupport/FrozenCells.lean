import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.CertifiedStates
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedResolutionExact

/-!
# The gray cells of a frozen round survive in the outer game

A round frozen by a recursive call recorded its gray cells against a localised server move; the
closure argument needs them to be genuinely new cells of the outer game.
`grayCharged_mem_localAlloc_imp_mem_family` transports an allocation from the localised move to
the family move, and `grayCharged_frozen_cell_transport_valid_of_A` and its chain form
`grayCharged_frozen_cell_transport_valid` transport a local gray cell. The frozen rounds
themselves form a harvest chain (`grayChargedStateAt_frozen_chain`,
`grayChargedHarvestChain_initial_mem_roundUnavailable`) of known phase-tagged shape
(`grayChargedStateAt_frozen_shape`) and known depth
(`grayChargedStateAt_frozen_eps_of_fine`, `grayChargedStateAt_frozen_depth_ub`,
`grayChargedStateAt_frozen_depth_bounds`).
-/

namespace Kolmogorov

/-- On the snapshot chain the ambient list embeds into every frozen round's
stored unavailable (v14 §9.2: each snapshot is `A ++ harvest`). -/
lemma grayChargedHarvestChain_initial_mem_roundUnavailable
    {n b L nn : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {frozen : GrayTailFrozen n b} {p : GrayTailRound n b}
    (hchain : GrayTailHarvestChain L nn A sm frozen) (hp : p ∈ frozen) :
    forall z, z ∈ A -> z ∈ p.unavailable := by
  intro z hz
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
  rw [← hkp, hchain k hk]
  exact List.mem_append_left _ hz

/-- A codeword allocated to a slot by the localised server move is allocated by the underlying
family move to the node that slot names. -/
lemma grayCharged_mem_localAlloc_imp_mem_family {n b D u : Nat}
    {sm : Nat -> FamilyServerMove} (p : GrayTailRound n b)
    (j : Fin p.slots.length) {d : BitString}
    (hd : d ∈ getFamilyAlloc
      (grayTailLocalServerMove D p.slots (sm u)) j.val []) :
    d ∈ getFamilyAlloc (sm u) (p.slots.get j).1.val
      [(p.slots.get j).2.1.val, (p.slots.get j).2.2.val] := by
  rw [getFamilyAlloc_grayTailLocalServerMove p.slots (sm u) j.val j.isLt []
    (by simp)] at hd
  have hd' := (mem_truncAlloc.mp hd).1
  simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'

/-- Section 8.3: a local gray cell of a frozen recursive round extends to a
new gray cell of the round's outer owner at the common final depth.  The
only fact about the round's `unavailable` list that is needed is that it
contains the ambient list `A`. -/
theorem grayCharged_frozen_cell_transport_valid_of_A
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hA : forall z, z ∈ A -> z ∈ p.unavailable)
    (hlow : e <= p.epsDepth)
    (hTU : p.serverTime <= U)
    (j : Fin p.slots.length) {cell w : BitString}
    (hcell : cell ∈ newGrayCellsList p.epsDepth (p.epsDepth + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime)) j.val []) p.unavailable)
    (hw : cell.length + w.length = e + grayTailNewLoss q L) :
    (cell ++ w) ∈ newGrayCellsList e (e + grayTailNewLoss q L)
      (getFamilyAlloc (sm U) (p.slots.get j).1.val []) A := by
  obtain ⟨hcellLen, hnear, hfresh⟩ := mem_newGrayCellsList.mp hcell
  rw [mem_newGrayCellsList]
  refine ⟨by simp [hw], ?_, ?_⟩
  · obtain ⟨z, hz, hzcomp⟩ := hnear
    have hzFamily := grayCharged_mem_localAlloc_imp_mem_family p j hz
    obtain ⟨root, hroot, hrootz⟩ :=
      exists_root_prefix_of_family_alloc hsm (p.slots.get j).1.isLt hTU
        (by
          intro c hc
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hc
          rcases hc with rfl | rfl
          · exact (p.slots.get j).2.1.isLt
          · exact (p.slots.get j).2.2.isLt) hzFamily
    refine ⟨root, hroot, ?_⟩
    have hcoarse : cell.take p.epsDepth <+: root ∨
        root <+: cell.take p.epsDepth := prefixComparable_of_common_extension hzcomp hrootz
    have htakePrefix : (cell ++ w).take e <+: cell.take p.epsDepth := by
      have htake : cell.take e <+: cell.take p.epsDepth := by
        simpa [List.take_take, min_eq_left hlow] using
          (List.take_prefix e (cell.take p.epsDepth))
      have hecell : e <= cell.length := by rw [hcellLen]; omega
      simpa [List.take_append_of_le_length hecell] using htake
    exact prefixComparable_of_prefix_of_prefixComparable htakePrefix hcoarse
  · rintro ⟨c, hc, hcomp⟩
    refine hfresh ⟨c, hA c hc, ?_⟩
    exact prefixComparable_of_prefix_of_prefixComparable
      (List.prefix_append cell w) hcomp

/-- Section 8.3, chain form: the round belongs to a frozen list with the
predecessor-snapshot harvest chain. -/
theorem grayCharged_frozen_cell_transport_valid
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {frozen : GrayTailFrozen n (grayTailBranch q L a e)}
    (hchain : GrayTailHarvestChain L n A sm frozen)
    {p : GrayTailRound n (grayTailBranch q L a e)} (hp : p ∈ frozen)
    (hlow : e <= p.epsDepth)
    (hTU : p.serverTime <= U)
    (j : Fin p.slots.length) {cell w : BitString}
    (hcell : cell ∈ newGrayCellsList p.epsDepth (p.epsDepth + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime)) j.val []) p.unavailable)
    (hw : cell.length + w.length = e + grayTailNewLoss q L) :
    (cell ++ w) ∈ newGrayCellsList e (e + grayTailNewLoss q L)
      (getFamilyAlloc (sm U) (p.slots.get j).1.val []) A :=
  grayCharged_frozen_cell_transport_valid_of_A hsm
    (grayChargedHarvestChain_initial_mem_roundUnavailable hchain hp) hlow hTU j
    hcell hw

/-- The rounds frozen by the charged controller form a harvest chain: consecutive rounds are
nested as the tail construction requires. -/
lemma grayChargedStateAt_frozen_chain
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} :
    GrayTailHarvestChain L n A sm
      (grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t).core.frozen := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t = st at hcert
  cases hcert with
  | advantage core hcore hsource hactive => exact (hcore.toCore (a := a) hsource).frozen_chain
  | spend pass core hspend => exact hspend.core.frozen_chain
  | done core hdone => exact hdone.core.frozen_chain

/-- The phase-tagged shape of every frozen round of the charged run. -/
lemma grayChargedStateAt_frozen_shape
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {p : GrayTailRound n b}
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen) :
    GrayChargedRoundShape q L a e sm p := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t = st at hcert hp
  cases hcert with
  | advantage core hcore hsource hactive =>
      exact ((hcore.toCore (a := a) hsource).round_valid p hp).2.2.2.2
  | spend pass core hspend => exact (hspend.core.round_valid p hp).2.2.2.2
  | done core hdone => exact (hdone.core.round_valid p hp).2.2.2.2

/-- The call depth clears the bin scale by at least five levels. -/
lemma grayCallDepth_ge_add_five (q e : Nat) :
    e + 5 <= grayCallDepth q e := by
  have hsize : 3 <= Nat.size (3 * q + 5) := by
    have h4 : 2 ^ 2 <= 3 * q + 5 := by omega
    have := Nat.lt_size.mpr h4
    omega
  unfold grayCallDepth
  omega

/-- The clamped spend scale never exceeds the bin scale by more than the
sub-root offset. -/
lemma grayChargedSpendEps_le_add_three
    {a e : Nat} (L pass : Nat) (hae : a <= e) :
    grayChargedSpendEps a L e pass <= e + 3 := by
  unfold grayChargedSpendEps grayChargedSpendAlphaDepth
  omega

/-- A frozen round at or above the call depth is an advantage round of the
descending fine schedule. -/
lemma grayChargedStateAt_frozen_eps_of_fine
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {p : GrayTailRound n b}
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth) :
    p.epsDepth = grayTailRoundEps q L e p.roundIndex := by
  rcases grayChargedStateAt_frozen_shape hp with ⟨hdepth, -⟩ |
    ⟨pass, -, hdepth, -, -⟩
  · exact hdepth
  · exfalso
    have hle : p.epsDepth <= e + 3 := by
      rw [hdepth]
      exact grayChargedSpendEps_le_add_three L pass hae
    have hcall := grayCallDepth_ge_add_five q e
    omega

/-- Every frozen round, of either phase, stays above the final loss floor. -/
lemma grayChargedStateAt_frozen_depth_ub
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {p : GrayTailRound n b}
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e) :
    p.epsDepth + L <= e + grayTailNewLoss q L := by
  have hLle : L <= grayTailNewLoss q L := by
    rw [grayTailNewLoss_eq]
    calc
      L = 1 * L := (one_mul L).symm
      _ <= 256 * (q + 1) ^ 2 * L := by
        have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
        exact Nat.mul_le_mul_right L hpos
      _ <= 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := Nat.le_add_right _ _
  rcases grayChargedStateAt_frozen_shape hp with ⟨hdepth, -⟩ |
    ⟨pass, -, hdepth, -, -⟩
  · rw [hdepth]
    have hdelta_eq : grayTailRoundEps q L e p.roundIndex + L =
        grayTailRoundDelta q L e p.roundIndex := rfl
    rw [hdelta_eq, grayTailNewLoss_eq]
    have hdelta_ub := grayTailRoundDelta_upper q L e p.roundIndex
    linarith
  · have hle : p.epsDepth <= e + 3 := by
      rw [hdepth]
      exact grayChargedSpendEps_le_add_three L pass hae
    have hq1 : 256 <= 256 * (q + 1) := by
      have := Nat.succ_le_succ (Nat.zero_le q)
      calc
        256 = 256 * 1 := (mul_one 256).symm
        _ <= 256 * (q + 1) := Nat.mul_le_mul_left 256 this
    have hq2 : L <= 256 * (q + 1) ^ 2 * L := by
      have hpos : 0 < 256 * (q + 1) ^ 2 := by positivity
      calc
        L = 1 * L := (one_mul L).symm
        _ <= 256 * (q + 1) ^ 2 * L := Nat.mul_le_mul_right L hpos
    rw [grayTailNewLoss_eq]
    omega

/-- A fine frozen round has epsilon depth between `e` and `e + grayTailNewLoss q L - L`, so its
transport depth `p.epsDepth + L` stays within `e + grayTailNewLoss q L`. -/
lemma grayChargedStateAt_frozen_depth_bounds
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {p : GrayTailRound n b}
    (hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth) :
    e <= p.epsDepth ∧ p.epsDepth + L <= e + grayTailNewLoss q L :=
  ⟨le_trans (le_grayCallDepth q e) hfine,
    grayChargedStateAt_frozen_depth_ub hp hae⟩

end Kolmogorov
