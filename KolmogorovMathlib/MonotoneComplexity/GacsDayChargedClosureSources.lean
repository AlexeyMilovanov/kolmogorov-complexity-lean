import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCollisions

/-!
# Transporting one accepted charged round to the common final depth

This file is the per-round half of the charged final charge transport.  An
accepted round `p` of the charged controller carries a certified *local*
charged gray goal at its own scales `(p.epsDepth, p.epsDepth + L)`.  From that
goal we read off one local designated charge `G`, split it into its recursive
owner fibres, and refine every local cell into the block of its extensions at
the common final depth `e + grayTailNewLoss q L`.

The resulting `GrayChargedChargeSource` records keep the owner information:
one record per recursive root of the round, tagged with the outer root that
owns it.  The three facts exported to the global ledger are

* `grayChargedSourceCharge_roundSources` — the flattened charge of the records
  is exactly `grayChargedTransportRound`;
* `grayChargedRoundSources_mass` — refinement is lossless;
* `grayChargedRoundSources_request_lower` / `_beta_lower` — the aggregate H3
  and H2 bounds of the round, counted once per accepted recursive call.

Nothing here uses owner tags for physical disjointness: all collision control
happens in `GacsDayChargedClosureLedger` from prefix incomparability.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ## Dyadic refinement of a coarse count -/

/-- Refining every cell of a coarse count to the final depth preserves mass. -/
lemma grayChargedMassOfCount_refine {d D count : Nat} (h : d <= D) :
    grayMassOfCount D (count * 2 ^ (D - d)) = grayMassOfCount d count := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : (2 : Rat) ^ k * (1 / 2 : Rat) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [grayMassOfCount, Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_add]
  calc (count : Rat) * 2 ^ k * ((1 / 2 : Rat) ^ d * (1 / 2 : Rat) ^ k)
      = (count : Rat) * (1 / 2 : Rat) ^ d * ((2 : Rat) ^ k * (1 / 2 : Rat) ^ k) := by
        ring
    _ = (count : Rat) * (1 / 2 : Rat) ^ d := by rw [hk, mul_one]

/-- Gray charge mass is nonnegative. -/
lemma grayChargedChargeMass_nonneg (d : Nat) (G : FamilyGrayCharge) :
    0 <= grayChargeMass d G := by
  unfold grayChargeMass grayMassOfCount
  positivity

/-! ## Flat maps over indexed families -/

/-- `List.flatMap f` equals mapping with `f` and then flattening. -/
lemma grayChargedList_flatMap_eq_flatMap_id {alpha beta : Type _}
    (l : List alpha) (f : alpha -> List beta) :
    l.flatMap f = (l.map f).flatMap id := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The length of a flattened list is the sum of the lengths of its parts. -/
lemma grayChargedList_length_flatMap {alpha beta : Type _}
    (l : List alpha) (f : alpha -> List beta) :
    (l.flatMap f).length = (l.map fun x => (f x).length).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-! ## The cylinder block of one local charge cell -/

/-- All depth-`delta` extensions of the local cells owned by one recursive
root, retagged with the outer root that owns the round slot. -/
def grayChargedTransportRoot (delta owner root : Nat) (G : FamilyGrayCharge) :
    FamilyGrayCharge :=
  (grayChargeAtRoot root G).flatMap fun z =>
    (allStrings (delta - z.2.length)).map fun w => (owner, z.2 ++ w)

/-- A pair belongs to the transported root charge exactly when it extends the string of a charge
at that root by an arbitrary word to depth `delta`, under the owner `owner`. -/
lemma mem_grayChargedTransportRoot {delta owner root : Nat} {G : FamilyGrayCharge}
    {z : Nat × BitString} :
    z ∈ grayChargedTransportRoot delta owner root G ↔
      exists source, source ∈ grayChargeAtRoot root G ∧
        z ∈ (allStrings (delta - source.2.length)).map
          fun w => (owner, source.2 ++ w) := by
  simp [grayChargedTransportRoot, List.mem_flatMap]

/-- Every cell of a transported root charge is owned by `owner`. -/
lemma grayChargedTransportRoot_owner {delta owner root : Nat} {G : FamilyGrayCharge}
    {z : Nat × BitString} (hz : z ∈ grayChargedTransportRoot delta owner root G) :
    z.1 = owner := by
  obtain ⟨source, -, hz⟩ := mem_grayChargedTransportRoot.mp hz
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz
  rfl

/-- Two extensions of two distinct bases of one common length never meet. -/
lemma grayChargedCylinder_disjoint_of_ne {owner owner' k k' d : Nat}
    {u v : BitString} (hu : u.length = d) (hv : v.length = d) (hne : u ≠ v) :
    List.Disjoint (((allStrings k).map fun w => (owner, u ++ w)).map Prod.snd)
      (((allStrings k').map fun w => (owner', v ++ w)).map Prod.snd) := by
  intro x hx hx'
  simp only [List.map_map, List.mem_map] at hx hx'
  obtain ⟨w, -, hw⟩ := hx
  obtain ⟨w', -, hw'⟩ := hx'
  apply hne
  have h : u ++ w = v ++ w' := by
    simpa using hw.trans hw'.symm
  have := congrArg (List.take d) h
  rwa [List.take_left' hu, List.take_left' hv] at this

/-- Transporting a charge whose strings are distinct and all of length `d` leaves the cells
pairwise distinct. -/
lemma grayChargedTransportRoot_nodup {delta owner root d : Nat}
    {G : FamilyGrayCharge}
    (hnodup : ((grayChargeAtRoot root G).map Prod.snd).Nodup)
    (hlen : forall z, z ∈ grayChargeAtRoot root G -> z.2.length = d) :
    ((grayChargedTransportRoot delta owner root G).map Prod.snd).Nodup := by
  rw [grayChargedTransportRoot, List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro z _
    simp only [List.map_map]
    refine (allStrings_nodup _).map ?_
    intro w w' h
    have h' : z.2 ++ w = z.2 ++ w' := by simpa using h
    exact List.append_cancel_left h'
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_map.mp hnodup)
    intro u v hu hv hne
    exact grayChargedCylinder_disjoint_of_ne (hlen u hu) (hlen v hv) hne

/-- Transporting a charge whose strings all have length `d` multiplies the number of cells by
`2 ^ (delta - d)`. -/
lemma grayChargedTransportRoot_length {delta owner root d : Nat}
    {G : FamilyGrayCharge}
    (hlen : forall z, z ∈ grayChargeAtRoot root G -> z.2.length = d) :
    (grayChargedTransportRoot delta owner root G).length =
      (grayChargeAtRoot root G).length * 2 ^ (delta - d) := by
  rw [grayChargedTransportRoot]
  generalize hL : grayChargeAtRoot root G = l at hlen
  clear hL
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : x.2.length = d := hlen x (by simp)
      have hxs : forall z, z ∈ xs -> z.2.length = d := by
        intro z hz
        exact hlen z (by simp [hz])
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        length_allStrings, hx, ih hxs, List.length_cons]
      ring

/-- Refining one owner fibre to the final depth preserves its mass. -/
lemma grayChargedTransportRoot_mass_of_charge
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth m D owner root : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (hdepth : deltaDepth <= D)
    (hvalid : familyGrayChargeAtB eta kappa alpha beta
      epsDepth deltaDepth m A c s G = true) :
    grayChargeMass D (grayChargedTransportRoot D owner root G) =
      grayChargeMass deltaDepth (grayChargeAtRoot root G) := by
  have hlen : forall z, z ∈ grayChargeAtRoot root G -> z.2.length = deltaDepth := by
    intro z hz
    exact (mem_newGrayCellsList.mp
      (familyGrayChargeAtB.cell hvalid (mem_grayChargeAtRoot.mp hz).1).2).1
  unfold grayChargeMass
  rw [grayChargedTransportRoot_length hlen]
  exact grayChargedMassOfCount_refine hdepth

/-! ## The transport of one whole accepted round -/

/-- The full transported charge of one accepted round: every recursive root of
the round contributes its own fibre, tagged with the outer root of its slot. -/
def grayChargedTransportRound {n b : Nat} (D : Nat)
    (slots : List (GrayTailSlot n b)) (G : FamilyGrayCharge) :
    FamilyGrayCharge :=
  (List.ofFn fun j : Fin slots.length =>
    grayChargedTransportRoot D (slots.get j).1.val j.val G).flatMap id

/-! ## Reading the local charge off a certified round -/

/-- The designated local charge of one certified charged round. -/
noncomputable def grayChargedLocalChargeOfGoal
    {q e epsRound deltaRound m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedTailGoalAtB q e epsRound deltaRound m A c s = true) :
    FamilyGrayCharge :=
  (familyChargedGrayGoalAtB.exists_charge h).choose

/-- The local charge extracted from a satisfied charged tail goal is a valid gray charge for the
parameters of that goal. -/
lemma grayChargedLocalChargeOfGoal_valid
    {q e epsRound deltaRound m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedTailGoalAtB q e epsRound deltaRound m A c s = true) :
    familyGrayChargeAtB 4 (halfAmplification q)
        (dyadicScale (grayCallDepth q e))
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
        epsRound deltaRound m A c s
        (grayChargedLocalChargeOfGoal h) = true :=
  (familyChargedGrayGoalAtB.exists_charge h).choose_spec.2

/-- Every accepted round of a certified charged state satisfies its own local
charged gray goal. -/
lemma grayChargedStateAt_frozen_goal
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p
      (grayChargedRunState q L a e n sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth) :
    grayChargedTailGoalAtB q e p.epsDepth (p.epsDepth + L)
      p.slots.length p.unavailable p.move
      (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime)) = true := by
  have hshape := grayChargedStateAt_frozen_shape
    (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
    (e := e) (t := t) (sigma := sigma) (A := A) (sm := sm) hp
  rcases hshape with ⟨-, hgoal, -, -, -⟩ | ⟨pass, -, hdepth, -, -, -⟩
  · exact hgoal
  · exfalso
    have hle := grayChargedSpendEps_le_add_three
      (a := a) (e := e) L pass hae
    have h5 := grayCallDepth_ge_add_five q e
    rw [hdepth] at hfine
    omega

/-- A frozen round below the call depth is a spend round; its coarse goal. -/
lemma grayChargedStateAt_frozen_spend_goal
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p
      (grayChargedRunState q L a e n sigma A sm t).core.frozen)
    (hcoarse : Not (grayCallDepth q e <= p.epsDepth)) :
    ∃ pass, pass < 8 ∧ p.epsDepth = grayChargedSpendEps a L e pass ∧
      grayChargedSpendGoalAtB q L a e pass
        p.slots.length p.unavailable p.move
          (grayTailLocalServerMove (p.epsDepth + L) p.slots
            (sm p.serverTime)) = true := by
  have hshape := grayChargedStateAt_frozen_shape
    (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
    (e := e) (t := t) (sigma := sigma) (A := A) (sm := sm) hp
  rcases hshape with ⟨hdepth, -, -, -, -⟩ | ⟨pass, hpass, hdepth, hgoal, -, -⟩
  · exfalso
    apply hcoarse
    rw [hdepth]
    exact grayTailRoundEps_lower q L e p.roundIndex
  · exact ⟨pass, hpass, hdepth, hgoal⟩

/-! ## The final displayed root request of a finished controller -/

/-- After the controller is done, the displayed root request is exactly the
charged root request read off the frozen entries. -/
lemma grayChargedRunMove_root_eq_of_done
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunState q L a e n sigma A sm U).phase = .done)
    (i : Fin n) :
    getFamilyReq (grayChargedRunMove q L a e n sigma A sm U) i.val [] =
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          (grayChargedRunState q L a e n sigma A sm U).core.frozen) i := by
  have hslots := grayChargedStateAt_slots_eq_nil_of_done
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm U hdone
  rw [show grayChargedRunMove q L a e n sigma A sm U =
      playClientFamily A n (grayChargedStrategy q L a e sigma) sm U from rfl,
    playClientFamily_grayChargedStrategy]
  simp only [grayChargedDisplayedMove, hdone, hslots]
  simp [getFamilyReq, familyClientMoveAt, grayChargedTailFamilyMove,
    List.getD_eq_getElem?_getD, i.isLt, grayTailEntries, grayTailSlotEntries]

/-! ## One frozen slot request never exceeds its outer root's final display -/

/-- One entry of a son base never exceeds the whole base. -/
lemma grayTailSonBase_single_le {n b : Nat}
    {entries : List (GrayTailSlot n b × ClientMove)}
    {i : Fin n} {c : Fin b} {x : GrayTailSlot n b × ClientMove}
    (hx : x ∈ entries) (hxi : x.1.1 = i) (hxc : x.1.2.1 = c)
    (hreq : forall p, p ∈ entries -> 0 <= getReq p.2 []) :
    getReq x.2 [] <= grayTailSonBase entries i c := by
  induction entries with
  | nil => simp at hx
  | cons y ys ih =>
      have hyreq : forall p, p ∈ ys -> 0 <= getReq p.2 [] :=
        fun p hp => hreq p (by simp [hp])
      have hrest : 0 <= grayTailSonBase ys i c := grayTailSonBase_nonneg_global hyreq
      unfold grayTailSonBase
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [ite_eq_left ⟨hxi, hxc⟩]
        have := hrest
        unfold grayTailSonBase at this
        linarith
      · have hle := ih hx hyreq
        unfold grayTailSonBase at hle
        split_ifs with h
        · have h0 : 0 <= getReq y.2 [] := hreq y (by simp)
          linarith
        · linarith

/-- The request displayed by one frozen recursive slot is at most the final
displayed request of the outer root that owns it. -/
theorem grayCharged_frozen_slot_req_le_final_root
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (j : Fin p.slots.length) :
    getFamilyReq p.move j.val [] <=
      getFamilyReq (grayChargedRunMove q L a e n sigma A sm U)
        (p.slots.get j).1.val [] := by
  classical
  set frozen := (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen
    with hfrozen
  set entries := grayTailFrozenEntries frozen with hentries
  set i : Fin n := (p.slots.get j).1 with hi
  set c : Fin (grayTailBranch q L a e) := (p.slots.get j).2.1 with hc
  -- nonnegativity of all displayed frozen requests
  have hreq : forall z, z ∈ entries -> 0 <= getReq z.2 [] := by
    intro z hz
    exact grayChargedStateAt_frozenEntries_req_nonneg
      (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a) (e := e)
      (t := T + 1) (sigma := sigma) (A := A) (sm := sm) z hz
  -- the entry of the slot `j` of the round `p`
  have hmemEntry : (p.slots.get j, familyClientMoveAt p.move j.val) ∈ entries := by
    rw [hentries, grayTailFrozenEntries, List.mem_flatMap]
    exact ⟨p, hp, by
      rw [grayTailSlotEntries]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  have hterm : getFamilyReq p.move j.val [] <= grayTailSonBase entries i c :=
    grayTailSonBase_single_le hmemEntry rfl rfl hreq
  -- the son request dominates the single term
  have hson : getFamilyReq p.move j.val [] <=
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i c := by
    by_cases hcs : c.val < grayChargedSourceCount a e
    · rw [grayChargedSonRequest_source i c hcs, grayTailSonRequest]
      by_cases hraise : grayChargedThreshold q e < grayTailSonBase entries i c
      · simp only [hraise, ite_true]
        rcases grayChargedStateAt_frozen_shape
            (n := n) (b := grayTailBranch q L a e) (q := q) (L := L)
            (a := a) (e := e) (t := T + 1) (sigma := sigma) (A := A)
            (sm := sm) hp with ⟨-, hgoal, -, -, -⟩ | ⟨pass, -, -, -, hpSlots, -⟩
        · have hub := (grayChargedTailGoalAtB_root_bounds hgoal j).2
          exact le_trans hub (dyadicScale_antitone (le_grayCallDepth q e))
        · exfalso
          have hge : grayChargedSourceCount a e <=
              ((p.slots.get j).2.1).val :=
            grayChargedSpendPairs_first_ge
              (hpSlots _ (List.get_mem _ _))
          rw [hc] at hcs
          omega
      · simp only [hraise, ite_false]
        exact hterm
    · rw [grayChargedSonRequest_spare i c (Nat.not_lt.mp hcs)]
      exact hterm
  -- and the root request dominates the son request
  have hnonneg : forall d : Fin (grayTailBranch q L a e),
      0 <= grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i d := by
    intro d
    by_cases hds : d.val < grayChargedSourceCount a e
    · rw [grayChargedSonRequest_source i d hds, grayTailSonRequest]
      by_cases hraise : grayChargedThreshold q e < grayTailSonBase entries i d
      · simp only [hraise, ite_true]
        exact (dyadicScale_pos e).le
      · simp only [hraise, ite_false]
        exact grayTailSonBase_nonneg_global hreq
    · rw [grayChargedSonRequest_spare i d (Nat.not_lt.mp hds)]
      exact grayTailSonBase_nonneg_global hreq
  have hroot : grayChargedSonRequest (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (dyadicScale e) entries i c <=
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i := by
    rw [grayChargedRootRequest]
    exact Finset.single_le_sum (f := fun d =>
      grayChargedSonRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i d)
      (fun d _ => hnonneg d) (Finset.mem_univ c)
  have hdisplay : getFamilyReq (grayChargedRunMove q L a e n sigma A sm U)
      i.val [] =
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e) entries i := by
    rw [grayChargedRunMove_root_eq_of_done (replay.done_stable U hU).1 i,
      (replay.done_stable U hU).2]
  rw [hdisplay]
  exact le_trans hson hroot

/-! ## The source records of one accepted round -/

/-- **Per-round transport.**  One `GrayChargedChargeSource` for every recursive
root of one accepted round, carrying the refined cylinder block of that root's
local designated cells at the common final depth. -/
noncomputable def grayChargedRoundSources
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    (phase : GrayChargedSourcePhase) :
    List (GrayChargedChargeSource q L a e n A
      (grayChargedRunMove q L a e n sigma A sm U) (sm U)) :=
  List.ofFn fun j : Fin p.slots.length =>
    { phase := phase
      round := p
      recursiveRoot := j.val
      recursiveRoot_lt := j.isLt
      outerRoot := (p.slots.get j).1
      owner_eq := rfl
      localCharge := grayChargedLocalChargeOfGoal
        (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)
      transported := grayChargedTransportRoot (e + grayTailNewLoss q L)
        (p.slots.get j).1.val j.val
        (grayChargedLocalChargeOfGoal (grayChargedStateAt_frozen_goal (L := L) hp hae hfine))
      transported_owner := fun _ hz => grayChargedTransportRoot_owner hz
      transported_valid := by
        intro z hz
        obtain ⟨source, hsource, hzc⟩ := mem_grayChargedTransportRoot.mp hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hzc
        have hvalid := grayChargedLocalChargeOfGoal_valid
          (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)
        have hcellmem := (mem_grayChargeAtRoot.mp hsource).1
        have hroot := (mem_grayChargeAtRoot.mp hsource).2
        have hcell := familyGrayChargeAtB.cell hvalid hcellmem
        have hbounds := grayChargedStateAt_frozen_depth_bounds
          (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
          (e := e) (t := T + 1) (sigma := sigma) (A := A) (sm := sm) hp hae hfine
        have hcellLen : source.2.length = p.epsDepth + L :=
          (mem_newGrayCellsList.mp hcell.2).1
        have hwLen : w.length = (e + grayTailNewLoss q L) - source.2.length :=
          (mem_allStrings _ _).mp hw
        refine ⟨(p.slots.get j).1.isLt, ?_⟩
        have hcell' : source.2 ∈ newGrayCellsList p.epsDepth (p.epsDepth + L)
            (getFamilyAlloc (grayTailLocalServerMove (p.epsDepth + L) p.slots
              (sm p.serverTime)) j.val []) p.unavailable := by
          rw [hroot] at hcell
          exact hcell.2
        exact grayCharged_frozen_cell_transport_valid hsm
          (grayChargedStateAt_frozen_chain
            (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
            (e := e) (t := T + 1) (sigma := sigma) (A := A) (sm := sm))
          hp hbounds.1
          (le_trans (replay.frozen_serverTime_le p hp) (by omega))
          j hcell' (by rw [hcellLen, hwLen, hcellLen]; omega)
      transported_cells_nodup := by
        have hvalid := grayChargedLocalChargeOfGoal_valid
          (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)
        refine grayChargedTransportRoot_nodup (d := p.epsDepth + L)
          (List.Nodup.sublist (List.filter_sublist.map Prod.snd)
            (familyGrayChargeAtB.cells_nodup hvalid)) ?_
        intro z hz
        exact (mem_newGrayCellsList.mp
          (familyGrayChargeAtB.cell hvalid (mem_grayChargeAtRoot.mp hz).1).2).1
      requestContribution :=
        grayChargeMass (e + grayTailNewLoss q L)
          (grayChargedTransportRoot (e + grayTailNewLoss q L)
            (p.slots.get j).1.val j.val
            (grayChargedLocalChargeOfGoal
              (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)))
          / halfAmplification q
      request_nonneg :=
        div_nonneg (grayChargedChargeMass_nonneg _ _) (halfAmplification_pos q).le
      recursive_lower := by
        rw [mul_div_cancel₀ _ (ne_of_gt (halfAmplification_pos q))]
      recursive_root_cap := by
        have hvalid := grayChargedLocalChargeOfGoal_valid
          (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)
        have hbounds := grayChargedStateAt_frozen_depth_bounds
          (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
          (e := e) (t := T + 1) (sigma := sigma) (A := A) (sm := sm) hp hae hfine
        rw [grayChargedTransportRoot_mass_of_charge hbounds.2 hvalid]
        refine le_trans (familyGrayChargeAtB.root hvalid j.isLt).2.2 ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by norm_num) (halfAmplification_pos q).le)
        exact grayCharged_frozen_slot_req_le_final_root replay hU hp j }

/-- The charge of the sources of a fine frozen round is the transport, to depth
`e + grayTailNewLoss q L`, of the local charge of that round. -/
lemma grayChargedSourceCharge_roundSources
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    (phase : GrayChargedSourcePhase) :
    grayChargedSourceCharge (grayChargedRoundSources hsm replay hU hp hae hfine phase) =
      grayChargedTransportRound (e + grayTailNewLoss q L) p.slots
        (grayChargedLocalChargeOfGoal
          (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)) := by
  rw [grayChargedSourceCharge, grayChargedRoundSources, grayChargedTransportRound,
    grayChargedList_flatMap_eq_flatMap_id, List.map_ofFn]
  rfl

/-! ## Mass and aggregate bounds of one transported round -/

/-- A charge whose owners all lie below `m` splits over its `m` root fibres. -/
lemma grayChargeAtRoot_length_sum {m : Nat} {G : FamilyGrayCharge}
    (h : forall z, z ∈ G -> z.1 < m) :
    ∑ j : Fin m, (grayChargeAtRoot j.val G).length = G.length := by
  classical
  induction G with
  | nil => simp [grayChargeAtRoot]
  | cons x xs ih =>
      have hx : x.1 < m := h x (by simp)
      have hxs : forall z, z ∈ xs -> z.1 < m := fun z hz => h z (by simp [hz])
      have hsplit : forall j : Fin m,
          (grayChargeAtRoot j.val (x :: xs)).length =
            (if x.1 = j.val then 1 else 0) + (grayChargeAtRoot j.val xs).length := by
        intro j
        by_cases hj : x.1 = j.val
        · simp only [grayChargeAtRoot, List.filter_cons, hj, beq_self_eq_true,
            List.length_cons, ite_eq_left]
          omega
        · simp [grayChargeAtRoot, hj]
      simp only [hsplit, Finset.sum_add_distrib, ih hxs, List.length_cons]
      have hone : ∑ j : Fin m, (if x.1 = j.val then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single (⟨x.1, hx⟩ : Fin m)]
        · simp
        · intro j _ hj
          have : x.1 ≠ j.val := by
            intro hval
            exact hj (Fin.ext hval.symm)
          simp [this]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hone]
      omega

/-- Transporting a valid round charge to a depth at least its own preserves its mass. -/
lemma grayChargedTransportRound_mass
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n b D : Nat}
    {slots : List (GrayTailSlot n b)}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (hdepth : deltaDepth <= D)
    (hvalid : familyGrayChargeAtB eta kappa alpha beta
      epsDepth deltaDepth slots.length A c s G = true) :
    grayChargeMass D (grayChargedTransportRound D slots G) =
      grayChargeMass deltaDepth G := by
  have hlength : (grayChargedTransportRound D slots G).length =
      ∑ j : Fin slots.length,
        (grayChargedTransportRoot D (slots.get j).1.val j.val G).length := by
    rw [grayChargedTransportRound, grayChargedList_length_flatMap, List.map_ofFn,
      List.sum_ofFn]
    rfl
  have hcelllen : forall (root : Nat) z, z ∈ grayChargeAtRoot root G ->
      z.2.length = deltaDepth := by
    intro root z hz
    exact (mem_newGrayCellsList.mp
      (familyGrayChargeAtB.cell hvalid (mem_grayChargeAtRoot.mp hz).1).2).1
  have hsum : (grayChargedTransportRound D slots G).length =
      G.length * 2 ^ (D - deltaDepth) := by
    rw [hlength]
    have : forall j : Fin slots.length,
        (grayChargedTransportRoot D (slots.get j).1.val j.val G).length =
          (grayChargeAtRoot j.val G).length * 2 ^ (D - deltaDepth) :=
      fun j => grayChargedTransportRoot_length (hcelllen j.val)
    simp only [this, ← Finset.sum_mul]
    rw [grayChargeAtRoot_length_sum
      (fun z hz => (familyGrayChargeAtB.cell hvalid hz).1)]
  unfold grayChargeMass
  rw [hsum]
  exact grayChargedMassOfCount_refine hdepth

/-- The mass of the charge of a fine frozen round's sources equals the mass of the local charge
of that round. -/
theorem grayChargedRoundSources_mass
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    (phase : GrayChargedSourcePhase) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge (grayChargedRoundSources hsm replay hU hp hae hfine phase)) =
      grayChargeMass (p.epsDepth + L)
        (grayChargedLocalChargeOfGoal
          (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)) := by
  rw [grayChargedSourceCharge_roundSources hsm replay hU hp hae hfine phase]
  have hbounds := grayChargedStateAt_frozen_depth_bounds
    (n := n) (b := grayTailBranch q L a e) (q := q) (L := L) (a := a)
    (e := e) (t := T + 1) (sigma := sigma) (A := A) (sm := sm) hp hae hfine
  exact grayChargedTransportRound_mass hbounds.2
    (grayChargedLocalChargeOfGoal_valid (grayChargedStateAt_frozen_goal (L := L) hp hae hfine))

/-- The charge of a fine frozen round's sources has mass at least `halfAmplification q` times the
total root request of that round. -/
theorem grayChargedRoundSources_request_lower
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    (phase : GrayChargedSourcePhase) :
    halfAmplification q * totalRootRequest p.slots.length p.move <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedRoundSources hsm replay hU hp hae hfine phase)) := by
  rw [grayChargedRoundSources_mass hsm replay hU hp hae hfine phase]
  exact (familyGrayChargeAtB.aggregate
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (L := L) hp hae hfine))).2

/-- The charge of a fine frozen round's sources has mass at least three quarters of
`dyadicScale (grayCallDepth q e)` per slot of the round. -/
theorem grayChargedRoundSources_beta_lower
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    (phase : GrayChargedSourcePhase) :
    (p.slots.length : Rat) * ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedRoundSources hsm replay hU hp hae hfine phase)) := by
  rw [grayChargedRoundSources_mass hsm replay hU hp hae hfine phase]
  exact (familyGrayChargeAtB.aggregate
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (L := L) hp hae hfine))).1

end Kolmogorov
