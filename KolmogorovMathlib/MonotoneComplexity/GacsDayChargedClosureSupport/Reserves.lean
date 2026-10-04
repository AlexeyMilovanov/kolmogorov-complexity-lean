import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailOwnerIndex
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.SourceLedger

/-!
# Reserve cylinders of the charged run

The cells the charged run sets aside to pay for its final charge. The bookkeeping facts about a
certified charged state come first — frozen requests are nonnegative, frozen son bases only grow,
the replayed advantage exit carries exactly the frozen list of its time, and after the controller
is done the displayed son request is the charged one. On the non-positive branch every resolved
source carries a late reserve (`grayChargedReplay_resolved_late_reserves`, with
`grayChargedReplay_raised_display_eq` for the raised sources), and the reserves at the common
final depth are valid and pairwise disjoint (`grayChargedReserveCylinder_valid`,
`grayChargedReserveCylinder_disjoint`), so their masses add up.
-/

namespace Kolmogorov

/-- Every request recorded in a frozen round of a certified charged state is
nonnegative: the recursive certificate keeps it above half a call scale. -/
lemma grayChargedStateAt_frozenEntries_req_nonneg
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (z : GrayTailSlot n b × ClientMove)
    (hz : z ∈ grayTailFrozenEntries
      (grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t).core.frozen) :
    0 <= getReq z.2 [] := by
  rw [grayTailFrozenEntries, List.mem_flatMap] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  have hshape : GrayChargedRoundShape q L a e sm p := by
    have hcert := grayChargedCertified_stateAt
      (n := n) (b := b) q L a e sigma A sm t
    generalize hst :
      grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t = st at hcert hp
    cases hcert with
    | advantage core hcore hsource hactive =>
        exact ((hcore.toCore (a := a) hsource).round_valid p hp).2.2.2.2
    | spend pass core hspend =>
        exact (hspend.core.round_valid p hp).2.2.2.2
    | done core hdone =>
        exact (hdone.core.round_valid p hp).2.2.2.2
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hzp
  rcases hshape with ⟨-, hgoal, -, -, -⟩ | ⟨pass, -, -, hgoal, -, -⟩
  · have hj := (grayChargedTailGoalAtB_root_bounds hgoal j).1
    have hpos : (0 : Rat) <= dyadicScale (grayCallDepth q e) / 2 :=
      div_nonneg (dyadicScale_pos _).le (by norm_num)
    have hnn : (0 : Rat) <= getFamilyReq p.move j.val [] := le_trans hpos hj
    simpa [getFamilyReq] using hnn
  · have hj := (grayChargedSpendGoalAtB_root_bounds hgoal j).1
    have hpos : (0 : Rat) <=
        dyadicScale (grayChargedSpendAlphaDepth a) / 2 :=
      div_nonneg (dyadicScale_pos _).le (by norm_num)
    have hnn : (0 : Rat) <= getFamilyReq p.move j.val [] := le_trans hpos hj
    simpa [getFamilyReq] using hnn

/-- Frozen son bases only grow along the charged run. -/
lemma grayChargedStateAt_frozenSonBase_mono
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {t u : Nat} (htu : t <= u)
    (i : Fin n) (c : Fin b) :
    grayTailFrozenSonBase
        (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm t).core.frozen i c <=
      grayTailFrozenSonBase
        (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm u).core.frozen i c := by
  obtain ⟨rest, hrest⟩ :=
    grayChargedStateAt_frozen_prefix_le q L a e sigma A sm htu
  have hsplit := grayTailFrozenSonBase_append_list
    (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen rest i c
  have hnonneg : 0 <= grayTailFrozenSonBase rest i c := by
    apply grayTailSonBase_nonneg_global
    intro z hz
    refine grayChargedStateAt_frozenEntries_req_nonneg (t := u) (q := q)
      (L := L) (a := a) (e := e) (sigma := sigma) (A := A) (sm := sm) z ?_
    rw [← hrest, grayTailFrozenEntries, List.flatMap_append]
    exact List.mem_append_right _ hz
  rw [hrest] at hsplit
  rw [hsplit]
  linarith

/-- The replayed advantage exit snapshot carries exactly the frozen list of the
controller state one step after the exit. -/
lemma grayChargedReplay_advantageTerminal_frozen_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    (grayChargedRunState q L a e n sigma A sm
        (replay.advantageExitTime + 1)).core.frozen =
      replay.advantageTerminal.frozen := by
  rw [replay.advantageTerminal_eq]
  change (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (replay.advantageExitTime + 1)).core.frozen = _
  rw [grayChargedStateAt_succ]
  simp only [grayChargedStep]
  rw [show (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm replay.advantageExitTime).phase = .advantage from
    replay.advantage_before]
  by_cases hdone : (grayChargedTailStep q L a e sigma A
      (grayChargedRunState q L a e n sigma A sm
        replay.advantageExitTime).core (sm replay.advantageExitTime)).done = true
  · simp only [hdone, ite_eq_left]
    unfold grayChargedStartSpend
    dsimp only
    split <;> rfl
  · simp only [hdone, Bool.false_eq_true, ite_false]

/-- After the controller is done, the displayed son request is exactly the
charged son request read off the frozen entries. -/
lemma grayChargedRunMove_son_eq_of_done
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunState q L a e n sigma A sm U).phase = .done)
    (i : Fin n) (c : Fin (grayTailBranch q L a e)) :
    getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) i.val [c.val] =
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          (grayChargedRunState q L a e n sigma A sm U).core.frozen) i c := by
  have hslots := grayChargedStateAt_slots_eq_nil_of_done
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm U hdone
  rw [show grayChargedRunMove q L a e n sigma A sm U =
      playClientFamily A n (grayChargedStrategy q L a e sigma) sm U from rfl,
    playClientFamily_grayChargedStrategy]
  simp only [grayChargedDisplayedMove, hdone, hslots]
  rw [show getFamilyReq
      (grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayChargedRunState q L a e n sigma A sm U).core.frozen [] [])
      i.val [c.val] = _ from
    getFamilyReq_grayChargedTailFamilyMove_son _ _ _ _ _ _ i c]
  simp [grayTailEntries, grayTailSlotEntries]

/-- A threshold-raised source displays exactly one coarse unit at every late
time.  This is the request that the non-positive branch must serve. -/
theorem grayChargedReplay_raised_display_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {z : Fin n × Fin (grayTailBranch q L a e)}
    (hz : z ∈ grayChargedReplayRaisedSources replay) :
    getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) z.1.val [z.2.val] =
      dyadicScale e := by
  classical
  have hmem := Finset.mem_filter.mp hz
  have hsrc : z.2.val < grayChargedSourceCount a e := hmem.2.1
  have hraise : grayChargedThreshold q e <
      grayTailFrozenSonBase replay.advantageTerminal.frozen z.1 z.2 := hmem.2.2
  have hdone := (replay.done_stable U hU).1
  have hstep : replay.advantageExitTime + 1 <= U :=
    le_trans (Nat.succ_le_succ replay.advantageExit_le) hU
  have hmono := grayChargedStateAt_frozenSonBase_mono
    (q := q) (L := L) (a := a) (e := e) (sigma := sigma) (A := A) (sm := sm)
    hstep z.1 z.2
  rw [grayChargedReplay_advantageTerminal_frozen_eq replay] at hmono
  have hfinal : grayChargedThreshold q e <
      grayTailSonBase (grayTailFrozenEntries
        (grayChargedRunState q L a e n sigma A sm U).core.frozen) z.1 z.2 :=
    lt_of_lt_of_le hraise hmono
  rw [grayChargedRunMove_son_eq_of_done hdone z.1 z.2]
  simp only [grayChargedSonRequest, hsrc, ite_eq_left, grayTailSonRequest]
  rw [ite_eq_left hfinal]

/-- Section 8.2 of the plan.  On the non-positive branch every resolved source
carries a genuine tail family reserve: a threshold-raised source displays a
full coarse unit and must therefore be served, while a server-resolved source
already has a reserve at the replayed advantage exit.  One common late horizon
`U` dominates all the selected service times and preserves the terminal client
display.  The reserve predicate itself stays at its true service time. -/
theorem grayChargedReplay_resolved_late_reserves
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    exists (U : Nat) (tau : Fin n × Fin (grayTailBranch q L a e) -> Nat)
      (res : Fin n × Fin (grayTailBranch q L a e) -> BitString),
      T + 1 <= U ∧
      grayChargedRunMove q L a e n sigma A sm U =
        grayChargedRunMove q L a e n sigma A sm T ∧
      ∀ z ∈ grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay,
        tau z <= U ∧ z.2.val < grayChargedSourceCount a e ∧
        IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
          (sm (tau z)) [z.2.val] (res z) := by
  classical
  have hex : ∀ z : Fin n × Fin (grayTailBranch q L a e),
      z ∈ grayChargedReplayRaisedSources replay ∪
        grayChargedReplayServerResolvedSources replay ->
      exists p : Nat × BitString,
        IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
          (sm p.1) [z.2.val] p.2 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hreq : dyadicScale e <=
          getFamilyReq (grayChargedRunMove q L a e n sigma A sm (T + 1))
            z.1.val [z.2.val] :=
        le_of_eq (grayChargedReplay_raised_display_eq replay le_rfl hz).symm
      obtain ⟨u, R, hR⟩ := grayCharged_exists_reserve_of_not_positive
        hsm hnotpos z.1.isLt (T + 1) [z.2.val] (by simp; omega)
        (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          subst hd
          exact z.2.isLt) hreq
      exact ⟨(u, R), hR⟩
    · have hsome := (Finset.mem_filter.mp hz).2.2.2
      obtain ⟨R, hR⟩ := (getTailFamilyReserve_isSome_iff _ _ _ _ _ _ _).mp hsome
      exact ⟨(replay.advantageExitTime, R), hR⟩
  choose! f hf using hex
  refine ⟨max (T + 1) ((grayChargedReplayRaisedSources replay ∪
      grayChargedReplayServerResolvedSources replay).sup
      (fun z => (f z).1)), fun z => (f z).1, fun z => (f z).2,
    le_max_left _ _, replay.move_stable _ (le_max_left _ _), ?_⟩
  intro z hz
  refine ⟨le_trans (Finset.le_sup (f := fun z => (f z).1) hz) (le_max_right _ _),
    ?_, hf z hz⟩
  rcases Finset.mem_union.mp hz with hz | hz
  · exact grayChargedRaisedSources_source_lt hz
  · exact grayChargedServerResolvedSources_source_lt hz

/-! ## Section 8.4: reserve cylinders at the common final depth

A reserve found at a source is a cylinder of depth `e`.  Its extension to the
final depth is a block of physically distinct cells owned by the source's outer
root; the block is valid against the common late server move, has total mass
exactly one coarse unit, and two blocks coming from distinct reserves never
meet. -/

/-- The depth-`delta` cylinder of a reserve, tagged with its owning root. -/
def grayChargedReserveCylinder (i delta : Nat) (R : BitString) : FamilyGrayCharge :=
  (allStrings (delta - R.length)).map fun s => (i, R ++ s)

/-- Every cell of a reserve cylinder is owned by the client `i` it was built for. -/
lemma grayChargedReserveCylinder_owner {i delta : Nat} {R : BitString}
    {z : Nat × BitString} (hz : z ∈ grayChargedReserveCylinder i delta R) : z.1 = i := by
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hz
  rfl

/-- The strings of a reserve cylinder are exactly the extensions of `R` to length `delta`. -/
lemma grayChargedReserveCylinder_snd (i delta : Nat) (R : BitString) :
    (grayChargedReserveCylinder i delta R).map Prod.snd =
      (allStrings (delta - R.length)).map fun s => R ++ s := by
  simp [grayChargedReserveCylinder, List.map_map, Function.comp]

/-- The strings of a reserve cylinder are pairwise distinct. -/
lemma grayChargedReserveCylinder_nodup (i delta : Nat) (R : BitString) :
    ((grayChargedReserveCylinder i delta R).map Prod.snd).Nodup := by
  rw [grayChargedReserveCylinder_snd]
  refine (allStrings_nodup _).map ?_
  intro s t hst
  exact List.append_cancel_left hst

/-- A reserve cylinder above `R` at depth `delta` has `2 ^ (delta - R.length)` cells. -/
lemma grayChargedReserveCylinder_length (i delta : Nat) (R : BitString) :
    (grayChargedReserveCylinder i delta R).length = 2 ^ (delta - R.length) := by
  simp [grayChargedReserveCylinder, length_allStrings]

/-- A reserve cylinder above a string of length at most `delta` carries mass
`dyadicScale R.length`, the mass of the cylinder of `R`. -/
lemma grayChargedReserveCylinder_mass {i delta : Nat} {R : BitString}
    (hlen : R.length <= delta) :
    grayChargeMass delta (grayChargedReserveCylinder i delta R) =
      dyadicScale R.length := by
  obtain ⟨k, rfl⟩ : exists k, delta = R.length + k := ⟨delta - R.length, by omega⟩
  rw [grayChargeMass, grayMassOfCount, grayChargedReserveCylinder_length,
    Nat.add_sub_cancel_left, dyadicScale, pow_add]
  push_cast
  have hk : ((2 : Rat)) ^ k * ((1 / 2 : Rat)) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  calc ((2 : Rat)) ^ k * (((1 / 2 : Rat)) ^ R.length * ((1 / 2 : Rat)) ^ k)
      = (((2 : Rat)) ^ k * ((1 / 2 : Rat)) ^ k) * ((1 / 2 : Rat)) ^ R.length := by
        ring
    _ = ((1 / 2 : Rat)) ^ R.length := by rw [hk, one_mul]

/-- Every cell of a reserve cylinder is a genuinely new gray cell of the owning
root at any later server move. -/
lemma grayChargedReserveCylinder_valid
    {e delta b n i tau U cc : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {R : BitString}
    (hsm : familyServerPlayLegal n b A sm)
    (hi : i < n) (hcc : cc < b) (hle : tau <= U) (hed : e <= delta)
    (hres : IsTailFamilyReserve e b A n i (sm tau) [cc] R)
    {z : Nat × BitString} (hz : z ∈ grayChargedReserveCylinder i delta R) :
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e delta (getFamilyAlloc (sm U) i []) A := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
  have hRlen : R.length = e := hres.1.1
  have hslen : s.length = delta - R.length := (mem_allStrings _ _).mp hs
  have hlegal := hsm.1 i hi
  -- the reserve meets the root allocation of its owner at the later time
  obtain ⟨v, hv, hvR⟩ := hres.1.2.1
  obtain ⟨w, hw, hwv⟩ :=
    allocationSubset_getAlloc_of_prefix (hlegal.1 tau)
      (x := ([] : GacsDayNode)) (y := [cc]) (List.nil_prefix)
      (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        subst hd
        exact hcc) v hv
  obtain ⟨w', hw', hw'w⟩ :=
    allocationSubset_mono_time hlegal hle [] w hw
  have hRw' : R <+: w' ∨ w' <+: R := by
    have hRw : R <+: w ∨ w <+: R := by
      rcases hvR with hRv | hvR
      · exact List.prefix_or_prefix_of_prefix hRv hwv
      · exact Or.inr (hwv.trans hvR)
    rcases hRw with hRw | hwR
    · exact List.prefix_or_prefix_of_prefix hRw hw'w
    · exact Or.inr (hw'w.trans hwR)
  have hRp : R <+: R ++ s := List.prefix_append _ _
  refine ⟨hi, ?_⟩
  rw [mem_newGrayCellsList]
  refine ⟨by simp [hslen]; omega, ?_, ?_⟩
  · refine ⟨w', ?_, ?_⟩
    · simpa [getFamilyAlloc] using hw'
    · rw [show (R ++ s).take e = R by
        rw [← hRlen]; simp]
      exact hRw'
  · rintro ⟨c, hc, hcomp⟩
    refine hres.1.2.2.2 c hc ?_
    rcases hcomp with hpc | hcp
    · exact Or.inl (hRp.trans hpc)
    · exact List.prefix_or_prefix_of_prefix hRp hcp

/-- Two distinct reserves of the same depth have disjoint cylinders, whatever
their owners.  Physical cells, not owner tags, are compared. -/
lemma grayChargedReserveCylinder_disjoint {i j delta e : Nat} {R S : BitString}
    (hR : R.length = e) (hS : S.length = e) (hne : R ≠ S) :
    List.Disjoint ((grayChargedReserveCylinder i delta R).map Prod.snd)
      ((grayChargedReserveCylinder j delta S).map Prod.snd) := by
  rw [grayChargedReserveCylinder_snd, grayChargedReserveCylinder_snd]
  intro p hp hq
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hq
  apply hne
  have h1 : (R ++ s).take e = R := by rw [← hR]; simp
  have h2 : (S ++ t).take e = S := by rw [← hS]; simp
  rw [← h1, ← h2, ht]



/-! ## Section 8.3: transporting a frozen round's local gray cells -/
lemma grayChargedFrozenChain_initial_mem_roundUnavailable
    {n b : Nat} {A : Allocation} {frozen : GrayTailFrozen n b}
    {p : GrayTailRound n b}
    (hchain : GrayTailFrozenChain A frozen) (hp : p ∈ frozen) :
    forall z, z ∈ A -> z ∈ p.unavailable := by
  induction frozen generalizing A with
  | nil => simp at hp
  | cons head tail ih =>
      obtain ⟨hhead, htail⟩ := hchain
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · intro z hz; rw [hhead]; exact hz
      · intro z hz
        exact ih htail hp z (by simp [hz])

end Kolmogorov
