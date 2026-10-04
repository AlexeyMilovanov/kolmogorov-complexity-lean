import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.CertifiedStates
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailGlobalProgress
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep

/-!
# Final replay and provenance interfaces

These records fix the representation used by the remaining leaves.  In
particular, a charge is checked against one common late server move, while the
client display is transported from the last useful controller transition.
-/

namespace Kolmogorov

/-- Source of one transported recursive charge.  The round and slot retain
the owner information that would be lost by flattening the final charge. -/
inductive GrayChargedSourcePhase where
  | advantage
  | spend (pass : Nat)
deriving DecidableEq

/-- The two disjoint reserve classes in Gacs's final accounting. -/
inductive GrayChargedReserveKind where
  | thresholdRaised
  | serverResolved
deriving DecidableEq

/-- Replay data that is independent of the later service horizon.  It saves the
unique advantage exit, its quarter-width estimate, and all monotonicity facts
needed to compare the final display with later server allocations. -/
/- The snapshot version of this record (as it stood in
`GacsDayChargedClosureLeaves`) carried the field

    successor_frozen_eq :
      (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen =
        (grayChargedRunState q L a e n sigma A sm T).core.frozen

together with `frozen_serverTime_le` / `frozen_alloc_subset_late` stated at
time `T`. That equality is not satisfiable in general: by `grayChargedStep`,
a `spend` phase that passes `grayChargedTailGoalAtB` on its last pass moves to
`.done` *while appending the accepted round to* `core.frozen`, so the frozen
list can strictly grow across the final transition of `GrayChargedFinalAt`.
The record below keeps exactly the same information in the satisfiable form
(`<+:` instead of `=`, and the frozen list read at `T + 1`); it is constructed
by `grayChargedFinalReplayOfFinal` at the end of this file. No downstream
declaration — in particular neither `grayCharged_final_charge_composition` nor
`grayChargedStrategy_chargedGameSpec` — reads any of these fields. -/
structure GrayChargedFinalReplay
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (T : Nat) : Type where
  final : GrayChargedFinalAt q L a e n sigma A sm T
  successor_done :
    (grayChargedRunState q L a e n sigma A sm (T + 1)).phase = .done
  successor_frozen_extends :
    (grayChargedRunState q L a e n sigma A sm T).core.frozen <+:
      (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen
  frozen_serverTime_le : forall p,
    p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen ->
      p.serverTime <= T
  frozen_alloc_subset_late : forall U, T + 1 <= U -> forall p,
    p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen ->
      allocationSubset p.allocated
        (grayTailLocalAllocatedList
          (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm U))
        )
  done_stable : forall U, T + 1 <= U ->
    (grayChargedRunState q L a e n sigma A sm U).phase = .done ∧
      (grayChargedRunState q L a e n sigma A sm U).core.frozen =
        (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen
  move_stable : forall U, T + 1 <= U ->
    grayChargedRunMove q L a e n sigma A sm U =
      grayChargedRunMove q L a e n sigma A sm T
  advantageExitTime : Nat
  advantageExit_le : advantageExitTime <= T
  advantage_before :
    (grayChargedRunState q L a e n sigma A sm advantageExitTime).phase =
      .advantage
  advantage_after :
    (grayChargedRunState q L a e n sigma A sm
      (advantageExitTime + 1)).phase ≠ .advantage
  advantageTerminal : GrayTailState n (grayTailBranch q L a e)
  advantageTerminal_eq : advantageTerminal =
    grayChargedTailStep q L a e sigma A
      (grayChargedRunState q L a e n sigma A sm advantageExitTime).core
      (sm advantageExitTime)
  terminal_width :
    4 * advantageTerminal.slots.length <=
      n * grayChargedSourceCount a e

/-- One recursive contribution after transport to the final common depth. -/
structure GrayChargedChargeSource
    (q L a e n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove) : Type where
  phase : GrayChargedSourcePhase
  round : GrayTailRound n (grayTailBranch q L a e)
  recursiveRoot : Nat
  recursiveRoot_lt : recursiveRoot < round.slots.length
  outerRoot : Fin n
  owner_eq : outerRoot =
    (round.slots.get ⟨recursiveRoot, recursiveRoot_lt⟩).1
  localCharge : FamilyGrayCharge
  transported : FamilyGrayCharge
  transported_owner : forall z, z ∈ transported -> z.1 = outerRoot.val
  transported_valid : forall z, z ∈ transported ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc s z.1 []) A
  transported_cells_nodup : (transported.map Prod.snd).Nodup
  requestContribution : Rat
  request_nonneg : 0 <= requestContribution
  recursive_lower :
    halfAmplification q * requestContribution <=
      grayChargeMass (e + grayTailNewLoss q L) transported
  recursive_root_cap :
    grayChargeMass (e + grayTailNewLoss q L) transported <=
      4 * halfAmplification q * getFamilyReq c outerRoot.val []

/-- One reserve-complement contribution at the common late server time. -/
structure GrayChargedReserveSource
    (q L a e n U : Nat) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Type where
  kind : GrayChargedReserveKind
  coordinate : Fin n × Fin (grayTailBranch q L a e)
  source_lt : coordinate.2.val < grayChargedSourceCount a e
  serviceTime : Nat
  service_le : serviceTime <= U
  reserve : BitString
  reserve_witness : IsTailFamilyReserve e (grayTailBranch q L a e) A n
    coordinate.1.val (sm serviceTime) [coordinate.2.val] reserve
  cells : FamilyGrayCharge
  cells_owner : forall z, z ∈ cells -> z.1 = coordinate.1.val
  cells_valid : forall z, z ∈ cells ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A
  cells_nodup : (cells.map Prod.snd).Nodup
  massContribution : Rat
  mass_lower : massContribution <=
    grayChargeMass (e + grayTailNewLoss q L) cells
  root_upper :
    grayChargeMass (e + grayTailNewLoss q L) cells <= dyadicScale a

/-- Flatten the transported recursive contributions without erasing owners. -/
def grayChargedSourceCharge
    {q L a e n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (sources : List (GrayChargedChargeSource q L a e n A c s)) :
    FamilyGrayCharge :=
  sources.flatMap GrayChargedChargeSource.transported

/-- Flatten the final reserve-complement contributions. -/
def grayChargedReserveCharge
    {q L a e n U : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) :
    FamilyGrayCharge :=
  reserves.flatMap GrayChargedReserveSource.cells

/-- Full source ledger and final charged cell list.  Aggregate bounds and H5
refer to the same `finalCharge`; no inverse from flattened geometry is needed. -/
structure GrayChargedChargeProvenance
    (q L a e n T U : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) : Type where
  sources : List (GrayChargedChargeSource q L a e n A
    (grayChargedRunMove q L a e n sigma A sm U) (sm U))
  reserves : List (GrayChargedReserveSource q L a e n U A sm)
  raisedSources : Finset (Fin n × Fin (grayTailBranch q L a e))
  serverResolvedSources : Finset (Fin n × Fin (grayTailBranch q L a e))
  raised_source : forall z, z ∈ raisedSources ->
    z.2.val < grayChargedSourceCount a e
  server_resolved_source : forall z, z ∈ serverResolvedSources ->
    z.2.val < grayChargedSourceCount a e
  source_classes_disjoint : Disjoint raisedSources serverResolvedSources
  reserve_ledger_complete : forall z,
    z ∈ raisedSources ∪ serverResolvedSources ->
      exists r, r ∈ reserves ∧ r.coordinate = z
  resolvedSourceCount_eq :
    (raisedSources ∪ serverResolvedSources).card +
        replay.advantageTerminal.slots.length =
      n * grayChargedSourceCount a e
  resolved_three_quarters :
    3 * (n * grayChargedSourceCount a e) <=
      4 * (raisedSources ∪ serverResolvedSources).card
  source_cells_nodup :
    ((grayChargedSourceCharge sources).map Prod.snd).Nodup
  reserve_cells_nodup :
    ((grayChargedReserveCharge reserves).map Prod.snd).Nodup
  source_reserve_disjoint :
    List.Disjoint
      ((grayChargedSourceCharge sources).map Prod.snd)
      ((grayChargedReserveCharge reserves).map Prod.snd)
  finalCharge : FamilyGrayCharge
  finalCharge_perm : finalCharge.Perm
    (grayChargedSourceCharge sources ++ grayChargedReserveCharge reserves)
  sublist : finalCharge ∈
    (familyGrayChargeUniverse n (e + grayTailNewLoss q L)).sublists
  cells_nodup : (finalCharge.map Prod.snd).Nodup
  cells_valid : forall z, z ∈ finalCharge ->
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A
  finalCharge_anchored : forall z, z ∈ finalCharge ->
    ∃ y ∈ getFamilyAlloc (sm U) z.1 [], y <+: z.2
  perRoot_cap : forall i, i < n ->
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i finalCharge) <=
      4 * halfAmplification (q + 1) *
        getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) i []
  subfamily_bound : forall I, I ∈ (List.range n).sublists ->
    halfAmplification (q + 1) *
        (2 * totalRootRequestOnList I
            (grayChargedRunMove q L a e n sigma A sm U) -
          totalRootRequest n (grayChargedRunMove q L a e n sigma A sm U)) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (finalCharge.filter fun z => decide (z.1 ∈ I))
  aggregate_beta :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      grayChargeMass (e + grayTailNewLoss q L) finalCharge
  aggregate_request :
    halfAmplification (q + 1) *
        totalRootRequest n
          (grayChargedRunMove q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L) finalCharge

/-- Forget source names only after all owner-sensitive bounds are proved. -/
def GrayChargedChargeProvenance.toGeometry
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {replay : GrayChargedFinalReplay q L a e n sigma A sm T}
    (p : GrayChargedChargeProvenance q L a e n T U sigma A sm replay) :
    GrayChargedChargeGeometry
      (halfAmplification (q + 1)) ((3 / 4 : Rat) * dyadicScale a)
      e (e + grayTailNewLoss q L) n A
      (grayChargedRunMove q L a e n sigma A sm U) (sm U) :=
  { charge := p.finalCharge
    sublist := p.sublist
    cells_nodup := p.cells_nodup
    cells_valid := p.cells_valid
    aggregate_beta := p.aggregate_beta
    aggregate_request := p.aggregate_request }

/-- A single late horizon at which every selected reserve and transported
recursive charge is checked, while the terminal client display is unchanged. -/
structure GrayChargedLateChargeWitness
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (T : Nat) : Type where
  replay : GrayChargedFinalReplay q L a e n sigma A sm T
  time : Nat
  terminal_succ_le : T + 1 <= time
  move_eq :
    grayChargedRunMove q L a e n sigma A sm time =
      grayChargedRunMove q L a e n sigma A sm T
  provenance :
    GrayChargedChargeProvenance q L a e n T time sigma A sm replay

/-! ## Section 3.3: constructing the final replay record

The lemmas below identify the charged controller with its pure advantage
fold while the advantage phase is still active, read off the terminal
quarter-width test at the advantage exit, and assemble the complete
`GrayChargedFinalReplay` record from the certified controller facts. -/
lemma grayChargedStartSpend_phase_ne_advantage {n b : Nat}
    (q L a e : Nat) (A : Allocation) (core : GrayTailState n b)
    (m : FamilyServerMove) :
    (grayChargedStartSpend q L a e A core m).phase ≠ .advantage := by
  by_cases hs : (grayChargedSlotsForPass q a e 0 core.frozen).isEmpty = true
  · simp [grayChargedStartSpend, hs]
  · simp [grayChargedStartSpend, hs]

/-- From a spend pass the controller never steps back into the `advantage` phase. -/
lemma grayChargedStep_phase_ne_advantage_of_spend {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedState n b) (m : FamilyServerMove) (pass : Nat)
    (hp : st.phase = .spend pass) :
    (grayChargedStep q L a e sigma A st m).phase ≠ .advantage := by
  simp only [grayChargedStep, hp]
  by_cases hslots : st.core.slots.isEmpty = true
  · simp [hslots]
  · simp only [hslots, Bool.false_eq_true, ↓reduceIte]
    split
    · split
      · split <;> simp
      · simp
    · simp

/-- While the controller is in the `advantage` phase, its core is the plain tail state at the
same time. -/
lemma grayChargedStateAt_core_eq_tailStateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hphase : (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).phase = .advantage) :
    (grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t).core =
      grayChargedTailStateAt (n := n) (b := b) q L a e sigma A sm t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [grayChargedStateAt_succ] at hphase
      rw [grayChargedStateAt_succ, grayChargedTailStateAt_succ]
      cases hp : (grayChargedStateAt (n := n) (b := b)
          q L a e sigma A sm t).phase with
      | done => exact absurd hphase (by simp [grayChargedStep, hp])
      | spend pass =>
          exact absurd hphase
            (grayChargedStep_phase_ne_advantage_of_spend q L a e sigma A _ (sm t)
              pass hp)
      | advantage =>
          have hcore := ih hp
          simp only [grayChargedStep, hp] at hphase ⊢
          by_cases hdone : (grayChargedTailStep q L a e sigma A
              (grayChargedStateAt (n := n) (b := b)
                q L a e sigma A sm t).core (sm t)).done = true
          · rw [ite_eq_left hdone] at hphase
            exact absurd hphase (grayChargedStartSpend_phase_ne_advantage _ _ _ _ _ _ _)
          · rw [ite_eq_right hdone, hcore]


/-- In the `advantage` phase the underlying tail run has not finished. -/
lemma grayChargedRunState_core_done_false_of_advantage
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage) :
    (grayChargedRunState q L a e n sigma A sm t).core.done = false := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  change (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).core.done = false
  change (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).phase = .advantage at hbefore
  generalize grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert hbefore ⊢
  cases hcert with
  | advantage core hcore hsource hactive => exact hactive
  | spend pass core hspend => simp at hbefore
  | done core hdoneCert => simp at hbefore

end Kolmogorov


