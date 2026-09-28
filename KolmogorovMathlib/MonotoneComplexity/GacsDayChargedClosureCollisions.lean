import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.FrozenCells
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport

/-!
# Global physical collision control for the charged closure

The reserves selected by the charged final ledger are found at *different*
server times, one per resolved source, and reserves are **not** persistent:
a string that is fresh at its own service time may well be allocated later.
This file proves the collision facts that are still available without any
persistence assumption.

The key observation is that the *witness* half of a reserve is monotone even
though the *freshness* half is not.  If `R` is a reserve of root `i` at node
`[c]` and time `tau`, then some allocated cell of `getFamilyAlloc (sm tau) i
[c]` is comparable with `R`; server monotonicity turns this into an allocated
cell of `getFamilyAlloc (sm tau') i [c]` comparable with `R` for every later
`tau'`.  A second reserve `S` living at the later time `tau'` and at a
*different* coordinate must avoid exactly such cells, so `R ≠ S`.  Taking the
two possible time orders gives unconditional pairwise distinctness of the
selected reserve strings across roots and rounds.
-/


namespace Kolmogorov

/-- Server monotonicity transports the witness clause of a reserve: if `R` is
comparable with an allocated cell of `getFamilyAlloc (sm tau) i x`, then it is
comparable with an allocated cell of `getFamilyAlloc (sm tau') i x` for every
later time `tau'`. -/
lemma isTailFamilyReserve_exists_late_witness
    {e b n i tau tau' : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {x : GacsDayNode} {R : BitString}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n) (hle : tau <= tau')
    (hR : IsTailFamilyReserve e b A n i (sm tau) x R) :
    exists w, w ∈ getFamilyAlloc (sm tau') i x ∧ (R <+: w ∨ w <+: R) := by
  obtain ⟨v, hv, hRv⟩ := hR.1.2.1
  obtain ⟨w, hw, hwv⟩ :=
    allocationSubset_mono_time (hsm.1 i hi) hle x v hv
  exact ⟨w, hw, prefixComparable_of_common_extension hRv hwv⟩

/-- Two reserves selected at distinct source coordinates are distinct strings,
even when they are found at different server times.  Only the earlier reserve
is transported; the later one is used at its own service time, so no reserve
persistence is assumed. -/
lemma isTailFamilyReserve_ne_of_ne_coordinate_of_le
    {e b n i j c c' tau tau' : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {R S : BitString}
    (hsm : familyServerPlayLegal n b A sm)
    (hi : i < n) (hc : c < b) (hle : tau <= tau')
    (hR : IsTailFamilyReserve e b A n i (sm tau) [c] R)
    (hS : IsTailFamilyReserve e b A n j (sm tau') [c'] S)
    (hne : ¬ (i = j ∧ c = c')) : R ≠ S := by
  rintro rfl
  obtain ⟨w, hw, hRw⟩ :=
    isTailFamilyReserve_exists_late_witness hsm hi hle hR
  by_cases hij : i = j
  · subst hij
    have hcc : c ≠ c' := fun h => hne ⟨rfl, h⟩
    refine hS.1.2.2.1 [c] ?_ ?_ w hw hRw
    · intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      exact hc
    · simp [hcc, Ne.symm hcc]
  · obtain ⟨u, hu, huw⟩ :=
      exists_root_prefix_of_family_alloc hsm hi (le_refl tau')
        (x := [c]) (by
          intro d hd
          simp only [List.mem_singleton] at hd
          subst hd
          exact hc) hw
    exact hS.2 i hi hij u hu (prefixComparable_of_common_extension hRw huw)

/-- Unconditional pairwise distinctness of reserves selected at distinct
source coordinates and arbitrary service times. -/
lemma isTailFamilyReserve_ne_of_ne_coordinate
    {e b n i j c c' tau tau' : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {R S : BitString}
    (hsm : familyServerPlayLegal n b A sm)
    (hi : i < n) (hj : j < n) (hc : c < b) (hc' : c' < b)
    (hR : IsTailFamilyReserve e b A n i (sm tau) [c] R)
    (hS : IsTailFamilyReserve e b A n j (sm tau') [c'] S)
    (hne : ¬ (i = j ∧ c = c')) : R ≠ S := by
  rcases Nat.le_total tau tau' with hle | hle
  · exact isTailFamilyReserve_ne_of_ne_coordinate_of_le hsm hi hc hle hR hS hne
  · exact Ne.symm
      (isTailFamilyReserve_ne_of_ne_coordinate_of_le hsm hj hc' hle hS hR
        (fun h => hne ⟨h.1.symm, h.2.symm⟩))


/-! ## Mass of a flattened charge -/

/-- Gray charge mass is additive over concatenation of charge lists. -/
lemma grayChargeMass_append (delta : Nat) (G H : FamilyGrayCharge) :
    grayChargeMass delta (G ++ H) =
      grayChargeMass delta G + grayChargeMass delta H := by
  simp only [grayChargeMass, grayMassOfCount, List.length_append]
  push_cast
  ring

/-- The gray charge mass of a flattened family of charge lists is the sum of the masses of the
parts. -/
lemma grayChargeMass_flatMap {alpha : Type _} (delta : Nat) (l : List alpha)
    (f : alpha -> FamilyGrayCharge) :
    grayChargeMass delta (l.flatMap f) =
      (l.map fun x => grayChargeMass delta (f x)).sum := by
  induction l with
  | nil => simp [grayChargeMass, grayMassOfCount]
  | cons x xs ih =>
      rw [List.flatMap_cons, grayChargeMass_append, ih]
      simp

/-! ## The concrete late reserve source family -/

/-- The reserve source attached to one resolved coordinate: the depth-`delta`
cylinder of the reserve found at its own service time, transported to the
common late horizon `U` by server monotonicity only. -/
noncomputable def grayChargedLateReserveSourceOf
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    GrayChargedReserveSource q L a e n U A sm where
  kind := kind
  coordinate := z
  source_lt := hsrc
  serviceTime := tau
  service_le := htau
  reserve := R
  reserve_witness := hres
  cells := grayChargedReserveCylinder z.1.val (e + grayTailNewLoss q L) R
  cells_owner := fun _ hz => grayChargedReserveCylinder_owner hz
  cells_valid := by
    intro w hw
    rw [grayChargedReserveCylinder, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    exact grayChargedReserveCylinder_valid hsm z.1.isLt z.2.isLt htau
      (Nat.le_add_right e (grayTailNewLoss q L)) hres
      (by rw [grayChargedReserveCylinder, List.mem_map]; exact ⟨s, hs, rfl⟩)
  cells_nodup := grayChargedReserveCylinder_nodup _ _ _
  massContribution := dyadicScale e
  mass_lower := by
    rw [grayChargedReserveCylinder_mass
      (by rw [hres.1.1]; exact Nat.le_add_right _ _), hres.1.1]
  root_upper := by
    rw [grayChargedReserveCylinder_mass
      (by rw [hres.1.1]; exact Nat.le_add_right _ _), hres.1.1]
    exact dyadicScale_antitone hae

/-- The late reserve source extracted at coordinate `z` is recorded at that coordinate. -/
@[simp] lemma grayChargedLateReserveSourceOf_coordinate
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    (grayChargedLateReserveSourceOf hsm hae kind z hsrc tau htau R hres).coordinate
      = z := rfl

/-- The cells of the late reserve source extracted at coordinate `z` are the reserve cylinder of
client `z.1` above `R` at depth `e + grayTailNewLoss q L`. -/
@[simp] lemma grayChargedLateReserveSourceOf_cells
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R) :
    (grayChargedLateReserveSourceOf hsm hae kind z hsrc tau htau R hres).cells
      = grayChargedReserveCylinder z.1.val (e + grayTailNewLoss q L) R := rfl

open Classical in
/-- **The concrete late reserve source family.**  On the non-positive branch
every resolved source of the final replay carries a real tail family reserve at
its own service time.  Their depth-`delta` cylinders form a list of
`GrayChargedReserveSource`s at one common late horizon `U`; the cylinders are
pairwise disjoint as sets of physical cells (no reserve persistence and no
conditional `R ≠ S` assumption is used), and their total mass is exactly one
coarse unit per resolved source. -/
theorem grayCharged_late_reserve_family
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    exists (U : Nat) (reserves : List (GrayChargedReserveSource q L a e n U A sm)),
      T + 1 <= U ∧
      grayChargedRunMove q L a e n sigma A sm U =
        grayChargedRunMove q L a e n sigma A sm T ∧
      (forall z, z ∈ grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay ->
        exists r, r ∈ reserves ∧ r.coordinate = z) ∧
      (forall r, r ∈ reserves -> r.coordinate ∈
        grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay) ∧
      ((grayChargedReserveCharge reserves).map Prod.snd).Nodup ∧
      grayChargeMass (e + grayTailNewLoss q L) (grayChargedReserveCharge reserves) =
        ((grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay).card : Rat) *
          dyadicScale e := by
  classical
  obtain ⟨U, tau, res, hU, hmove, hall⟩ :=
    grayChargedReplay_resolved_late_reserves hsm hnotpos replay
  set S := grayChargedReplayRaisedSources replay ∪
    grayChargedReplayServerResolvedSources replay with hSdef
  refine ⟨U, S.toList.attach.map fun zz =>
    grayChargedLateReserveSourceOf hsm hae
      (if zz.1 ∈ grayChargedReplayRaisedSources replay then
        GrayChargedReserveKind.thresholdRaised
      else GrayChargedReserveKind.serverResolved)
      zz.1 (hall zz.1 (Finset.mem_toList.mp zz.2)).2.1
      (tau zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).1
      (res zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2,
    hU, hmove, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨_, List.mem_map.mpr
      ⟨⟨z, Finset.mem_toList.mpr hz⟩, List.mem_attach _ _, rfl⟩, rfl⟩
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    exact Finset.mem_toList.mp zz.2
  · rw [grayChargedReserveCharge, List.map_flatMap, List.flatMap_map]
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro zz _
      exact grayChargedReserveCylinder_nodup _ _ _
    · refine List.Pairwise.imp ?_ (List.nodup_attach.mpr (Finset.nodup_toList S))
      intro zz zz' hne
      have hcoord : zz.1 ≠ zz'.1 := fun h => hne (Subtype.ext h)
      have hpair : ¬ (zz.1.1.val = zz'.1.1.val ∧ zz.1.2.val = zz'.1.2.val) := by
        rintro ⟨h1, h2⟩
        exact hcoord (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      have hR' := (hall zz'.1 (Finset.mem_toList.mp zz'.2)).2.2
      have hne' : res zz.1 ≠ res zz'.1 :=
        isTailFamilyReserve_ne_of_ne_coordinate hsm zz.1.1.isLt zz'.1.1.isLt
          zz.1.2.isLt zz'.1.2.isLt hR hR' hpair
      exact grayChargedReserveCylinder_disjoint hR.1.1 hR'.1.1 hne'
  · rw [grayChargedReserveCharge, grayChargeMass_flatMap]
    refine (List.sum_eq_card_nsmul _ (dyadicScale e) ?_).trans ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      simp only [grayChargedLateReserveSourceOf_cells]
      rw [grayChargedReserveCylinder_mass
        (by rw [hR.1.1]; exact Nat.le_add_right _ _), hR.1.1]
    · simp [nsmul_eq_mul]

/-! ## Reordering a valid charge into the charge universe

The `sublist` field of `GrayChargedChargeProvenance` asks for an *ordered*
subsequence of `familyGrayChargeUniverse n delta`, which is grouped by root.
Any nodup charge whose cells are valid is a subsequence of the universe *up to
permutation*, and every quantity the final Boolean certificate reads off a
charge (its cell multiset, its total mass, and its per-root masses) is
permutation invariant.  These lemmas package that fact. -/

/-- Gray charge mass depends only on the multiset of charges, not on their order. -/
lemma grayChargeMass_congr_perm {delta : Nat} {G H : FamilyGrayCharge}
    (h : G.Perm H) : grayChargeMass delta G = grayChargeMass delta H := by
  simp [grayChargeMass, grayMassOfCount, h.length_eq]

/-- Selecting the charges at a fixed root respects permutation of the charge list. -/
lemma grayChargeAtRoot_perm {i : Nat} {G H : FamilyGrayCharge}
    (h : G.Perm H) : (grayChargeAtRoot i G).Perm (grayChargeAtRoot i H) :=
  h.filter _

/-- The mass of the charges at a fixed root depends only on the multiset of charges. -/
lemma grayChargeMass_grayChargeAtRoot_congr_perm
    {delta i : Nat} {G H : FamilyGrayCharge} (h : G.Perm H) :
    grayChargeMass delta (grayChargeAtRoot i G) =
      grayChargeMass delta (grayChargeAtRoot i H) :=
  grayChargeMass_congr_perm (grayChargeAtRoot_perm h)

/-- A charge with distinct cells and valid cell lengths is, up to a
permutation, an ordered subsequence of the charge universe. -/
lemma exists_mem_sublists_familyGrayChargeUniverse_perm
    {n delta : Nat} {G : FamilyGrayCharge}
    (hnodup : (G.map Prod.snd).Nodup)
    (hvalid : forall z, z ∈ G -> z.1 < n ∧ z.2.length = delta) :
    exists G', G' ∈ (familyGrayChargeUniverse n delta).sublists ∧ G'.Perm G := by
  have hG : G.Nodup := hnodup.of_map _
  have hsub : G ⊆ familyGrayChargeUniverse n delta := by
    intro z hz
    exact mem_familyGrayChargeUniverse.mpr (hvalid z hz)
  obtain ⟨G', hperm, hsl⟩ := List.subperm_of_subset hG hsub
  exact ⟨G', List.mem_sublists.mpr hsl, hperm⟩

/-! ## The ordering constraint carried by the `sublist` field

`familyGrayChargeUniverse n delta` lists the cells of root `0` first, then
those of root `1`, and so on.  Consequently the owner tags along *any*
subsequence of the universe are non-decreasing.  Because
`GrayChargedChargeProvenance` asks for `finalCharge` to be such a subsequence
*and* to be literally `grayChargedSourceCharge sources ++
grayChargedReserveCharge reserves`, every transported recursive cell must be
owned by a root that is `<=` the root of every selected reserve cell.  This is
a genuine global constraint on any admissible source/reserve ledger, and it is
recorded here as a proved fact rather than left implicit. -/

/-- The universe of family gray charges is enumerated with nondecreasing root index. -/
lemma familyGrayChargeUniverse_pairwise_root_le (n delta : Nat) :
    (familyGrayChargeUniverse n delta).Pairwise
      (fun z w : Nat × BitString => z.1 <= w.1) := by
  refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
  · intro i _
    refine List.pairwise_of_forall_mem_list ?_
    intro x hx y hy
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    exact le_rfl
  · refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro i j hij x hx y hy
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    exact Nat.le_of_lt hij

/-- Every sublist of the family gray charge universe again has nondecreasing root index. -/
lemma pairwise_root_le_of_mem_sublists_familyGrayChargeUniverse
    {n delta : Nat} {G : FamilyGrayCharge}
    (hG : G ∈ (familyGrayChargeUniverse n delta).sublists) :
    G.Pairwise (fun z w : Nat × BitString => z.1 <= w.1) :=
  (familyGrayChargeUniverse_pairwise_root_le n delta).sublist
    (List.mem_sublists.mp hG)

/-- Every transported recursive cell of an admissible provenance is owned by a
root no larger than the root of every selected reserve cell. -/
theorem grayChargedChargeProvenance_source_root_le_reserve_root
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {replay : GrayChargedFinalReplay q L a e n sigma A sm T}
    (p : GrayChargedChargeProvenance q L a e n T U sigma A sm replay)
    (hordered : p.finalCharge =
      grayChargedSourceCharge p.sources ++
        grayChargedReserveCharge p.reserves)
    {zs zr : Nat × BitString}
    (hzs : zs ∈ grayChargedSourceCharge p.sources)
    (hzr : zr ∈ grayChargedReserveCharge p.reserves) :
    zs.1 <= zr.1 := by
  have hpair := pairwise_root_le_of_mem_sublists_familyGrayChargeUniverse p.sublist
  rw [hordered] at hpair
  exact (List.pairwise_append.mp hpair).2.2 zs hzs zr hzr

end Kolmogorov
