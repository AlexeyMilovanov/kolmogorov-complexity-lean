import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustFamily

/-!
# Finite designated-gray certificates for the Gacs-Day induction

Gacs's strengthened induction hypothesis designates a bounded subset of the
newly gray cells for every family root.  The designated cells, rather than all
gray cells, satisfy the per-root upper bound used to pay for reserve overlap.
This file records that finite witness without changing the public strategy API.
-/

namespace Kolmogorov

/-- A final-depth gray cell together with the family root charged for it. -/
abbrev FamilyGrayCharge := List (Nat × BitString)

/-- The finite universe from which a charge certificate is selected. -/
def familyGrayChargeUniverse (n deltaDepth : Nat) : FamilyGrayCharge :=
  (List.range n).flatMap fun i =>
    (allStrings deltaDepth).map fun p => (i, p)

/-- The part of a charge assigned to one family root. -/
def grayChargeAtRoot (i : Nat) (G : FamilyGrayCharge) : FamilyGrayCharge :=
  G.filter fun z => z.1 == i

/-- The cells, with their owner tag erased, assigned to one family root. -/
def grayChargeCellsAtRoot (i : Nat) (G : FamilyGrayCharge) : List BitString :=
  (grayChargeAtRoot i G).map Prod.snd

/-- Dyadic mass of a finite list of final-depth charged cells. -/
def grayChargeMass (deltaDepth : Nat) (G : FamilyGrayCharge) : Rat :=
  grayMassOfCount deltaDepth G.length

/-- Executable global uniqueness test for charged final cells. -/
def grayChargeCellsUniqueB (G : FamilyGrayCharge) : Bool :=
  decide ((G.map Prod.snd).dedup = G.map Prod.snd)

/-- The decidable uniqueness test on a charge holds exactly when its cells are pairwise distinct. -/
lemma grayChargeCellsUniqueB_eq_true_iff {G : FamilyGrayCharge} :
    grayChargeCellsUniqueB G = true ↔ (G.map Prod.snd).Nodup := by
  simp [grayChargeCellsUniqueB, List.dedup_eq_self]

/-- Gacs's designated-gray invariant at one fixed play stage.

The two nodup clauses make every final cell globally owned by at most one root.
The request window is (H1,H4), the local upper bound is (H5), the next two
inequalities are (H2,H3), and the final conjunct is Day's hereditary subfamily
inequality (outcome (ii)(c) of his TAMS 2011 strategy definition): no subfamily
may carry disproportionately little of the designated mass. -/
def familyGrayChargeAtB (eta kappa alpha beta : Rat)
    (epsDepth deltaDepth n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove)
    (G : FamilyGrayCharge) : Bool :=
  grayChargeCellsUniqueB G &&
    G.all (fun z =>
      decide (z.1 < n) &&
        decide (z.2 ∈ newGrayCellsList epsDepth deltaDepth
          (getFamilyAlloc s z.1 []) A)) &&
    (List.range n).all (fun i =>
      decide (alpha / 2 ≤ getFamilyReq c i []) &&
        decide (getFamilyReq c i [] ≤ alpha) &&
        decide (grayChargeMass deltaDepth (grayChargeAtRoot i G) ≤
          eta * kappa * getFamilyReq c i [])) &&
    decide ((n : Rat) * beta ≤ grayChargeMass deltaDepth G) &&
    decide (kappa * totalRootRequest n c ≤ grayChargeMass deltaDepth G) &&
    (List.range n).sublists.all (fun I =>
      decide (kappa *
        (2 * totalRootRequestOnList I c - totalRootRequest n c) ≤
          grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈ I))))

/-- The executable charged gray goal at one play stage: the plain gray goal
`familyGrayGoalAtB` holds for the family's root allocations, *and* some sublist of
`familyGrayChargeUniverse n deltaDepth` is a valid designated charge.  Keeping the plain
goal as an explicit conjunct makes forgetting the internal certificate definitional. -/
def familyChargedGrayGoalAtB (eta kappa alpha beta : Rat)
    (epsDepth deltaDepth n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyGrayGoalAtB kappa beta epsDepth deltaDepth n A c
      (familyAllocatedOnList (List.range n) s) &&
    (familyGrayChargeUniverse n deltaDepth).sublists.any
      (familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s)

/-- The charged gray goal over a whole play: at some time `T`, the moves `cm T` and `sm T`
pass the executable test `familyChargedGrayGoalAtB`. -/
def familyChargedGrayGoal (eta kappa alpha beta : Rat)
    (epsDepth deltaDepth n : Nat) (A : Allocation)
    (cm : Nat → FamilyClientMove) (sm : Nat → FamilyServerMove) : Prop :=
  ∃ T, familyChargedGrayGoalAtB eta kappa alpha beta epsDepth deltaDepth n A
    (cm T) (sm T) = true

/-- A round meeting the charged gray goal meets the plain gray goal for the same parameters. -/
lemma familyChargedGrayGoalAtB.to_familyGrayGoalAtB
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    (h : familyChargedGrayGoalAtB eta kappa alpha beta epsDepth deltaDepth n A c s = true) :
    familyGrayGoalAtB kappa beta epsDepth deltaDepth n A c
      (familyAllocatedOnList (List.range n) s) = true := by
  unfold familyChargedGrayGoalAtB at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- A round meeting the charged gray goal carries a witnessing charge inside the charge universe. -/
lemma familyChargedGrayGoalAtB.exists_charge
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    (h : familyChargedGrayGoalAtB eta kappa alpha beta epsDepth deltaDepth n A c s = true) :
    ∃ G ∈ (familyGrayChargeUniverse n deltaDepth).sublists,
      familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true := by
  unfold familyChargedGrayGoalAtB at h
  simp only [Bool.and_eq_true] at h
  simpa only [List.any_eq_true] using h.2

/-- A valid gray charge lists each of its entries once. -/
lemma familyGrayChargeAtB.nodup
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true) :
    G.Nodup := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, grayChargeCellsUniqueB_eq_true_iff,
    decide_eq_true_eq] at h
  apply List.Nodup.of_map Prod.snd
  aesop

/-- A valid gray charge has pairwise distinct cells. -/
lemma familyGrayChargeAtB.cells_nodup
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true) :
    (G.map Prod.snd).Nodup := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, grayChargeCellsUniqueB_eq_true_iff,
    decide_eq_true_eq] at h
  aesop

/-- A valid gray charge has mass at least `n * beta` and at least `kappa` times the total root
request. -/
lemma familyGrayChargeAtB.aggregate
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true) :
    (n : Rat) * beta ≤ grayChargeMass deltaDepth G ∧
      kappa * totalRootRequest n c ≤ grayChargeMass deltaDepth G := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

/-- The charge universe consists of the pairs of a client below `n` and a string of depth
`deltaDepth`. -/
lemma mem_familyGrayChargeUniverse {n deltaDepth : Nat} {z : Nat × BitString} :
    z ∈ familyGrayChargeUniverse n deltaDepth ↔ z.1 < n ∧ z.2.length = deltaDepth := by
  simp only [familyGrayChargeUniverse, List.mem_flatMap, List.mem_range,
    List.mem_map, mem_allStrings]
  constructor
  · rintro ⟨i, hi, p, hp, rfl⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨z.1, hi, z.2, hp, rfl⟩

/-- The charge universe lists each pair once. -/
lemma familyGrayChargeUniverse_nodup (n deltaDepth : Nat) :
    (familyGrayChargeUniverse n deltaDepth).Nodup := by
  classical
  rw [familyGrayChargeUniverse, List.nodup_flatMap]
  constructor
  · intro i hi
    exact (allStrings_nodup deltaDepth).map fun p q h =>
      congrArg Prod.snd h
  · refine List.nodup_range.imp ?_
    intro i j hij
    change List.Disjoint
      ((allStrings deltaDepth).map fun p => (i, p))
      ((allStrings deltaDepth).map fun p => (j, p))
    rw [List.disjoint_left]
    intro z hzi hzj
    simp only [List.mem_map] at hzi hzj
    obtain ⟨p, -, rfl⟩ := hzi
    obtain ⟨q, -, hq⟩ := hzj
    exact hij (congrArg Prod.fst hq.symm)

/-- Canonical sublist representation of a finite set of tagged charge cells. -/
def canonicalGrayCharge (n deltaDepth : Nat)
    (F : Finset (Nat × BitString)) : FamilyGrayCharge :=
  (familyGrayChargeUniverse n deltaDepth).filter fun z => decide (z ∈ F)

/-- The canonical form of a finite set of cells is a sublist of the charge universe. -/
lemma canonicalGrayCharge_sublist (n deltaDepth : Nat)
    (F : Finset (Nat × BitString)) :
    List.Sublist (canonicalGrayCharge n deltaDepth F)
      (familyGrayChargeUniverse n deltaDepth) :=
  List.filter_sublist

/-- The canonical form of a finite set of cells lists each entry once. -/
lemma canonicalGrayCharge_nodup (n deltaDepth : Nat)
    (F : Finset (Nat × BitString)) :
    (canonicalGrayCharge n deltaDepth F).Nodup :=
  (familyGrayChargeUniverse_nodup n deltaDepth).filter _

/-- For a set of cells inside the universe, the canonical form has exactly those members. -/
lemma mem_canonicalGrayCharge {n deltaDepth : Nat}
    {F : Finset (Nat × BitString)}
    (hF : ∀ z ∈ F, z.1 < n ∧ z.2.length = deltaDepth)
    {z : Nat × BitString} :
    z ∈ canonicalGrayCharge n deltaDepth F ↔ z ∈ F := by
  classical
  simp only [canonicalGrayCharge, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hz
    exact ⟨mem_familyGrayChargeUniverse.mpr (hF z hz), hz⟩

/-- If distinct cells of the set carry distinct strings, the canonical form has distinct cells. -/
lemma canonicalGrayCharge_cells_nodup {n deltaDepth : Nat}
    {F : Finset (Nat × BitString)}
    (hinj : ∀ z ∈ F, ∀ z' ∈ F, z.2 = z'.2 → z = z') :
    ((canonicalGrayCharge n deltaDepth F).map Prod.snd).Nodup := by
  apply (canonicalGrayCharge_nodup n deltaDepth F).map_on
  intro z hz z' hz' heq
  exact hinj z (by
    exact decide_eq_true_eq.mp (List.mem_filter.mp hz).2) z' (by
    exact decide_eq_true_eq.mp (List.mem_filter.mp hz').2) heq

/-- The charge at root `i` consists of the entries of the charge tagged with `i`. -/
@[simp] lemma mem_grayChargeAtRoot {i : Nat} {G : FamilyGrayCharge}
    {z : Nat × BitString} :
    z ∈ grayChargeAtRoot i G ↔ z ∈ G ∧ z.1 = i := by
  simp [grayChargeAtRoot, and_comm]

/-- Every cell of a valid gray charge belongs to a client below `n` and lies in the new gray area
of that client. -/
lemma familyGrayChargeAtB.cell
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true)
    {z : Nat × BitString} (hz : z ∈ G) :
    z.1 < n ∧
      z.2 ∈ newGrayCellsList epsDepth deltaDepth (getFamilyAlloc s z.1 []) A := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases z with ⟨i, p⟩
  exact h.1.1.1.1.2 (i, p) hz

/-- For a valid gray charge, every client requests between `alpha / 2` and `alpha` at the root,
and the charge at that root has mass at most `eta * kappa` times the root request. -/
lemma familyGrayChargeAtB.root
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true)
    {i : Nat} (hi : i < n) :
    alpha / 2 ≤ getFamilyReq c i [] ∧
      getFamilyReq c i [] ≤ alpha ∧
      grayChargeMass deltaDepth (grayChargeAtRoot i G) ≤
        eta * kappa * getFamilyReq c i [] := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hall : ∀ i ∈ List.range n,
      (alpha / 2 ≤ getFamilyReq c i [] ∧
        getFamilyReq c i [] ≤ alpha) ∧
        grayChargeMass deltaDepth (grayChargeAtRoot i G) ≤
          eta * kappa * getFamilyReq c i [] := by
    aesop
  have hi' := hall i (List.mem_range.mpr hi)
  exact ⟨hi'.1.1, hi'.1.2, hi'.2⟩

/-- Filtering by a disjunction of exclusive Boolean predicates splits the
count. -/
lemma length_filter_or {alpha : Type*} (l : List alpha) (p q : alpha -> Bool)
    (hpq : forall a, a ∈ l -> ¬ (p a = true ∧ q a = true)) :
    (l.filter fun a => p a || q a).length =
      (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail := ih fun b hb => hpq b (List.mem_cons_of_mem a hb)
      have hhead := hpq a (List.mem_cons_self ..)
      rw [List.filter_cons, List.filter_cons, List.filter_cons]
      cases hp : p a <;> cases hq : q a <;>
        simp_all <;> omega

/-- Filtering a charge by a nodup root list splits into per-root filters. -/
lemma grayChargeMass_filter_mem {deltaDepth : Nat}
    {G : FamilyGrayCharge} {I : List Nat} (hI : I.Nodup) :
    grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈ I)) =
      (I.map fun i =>
        grayChargeMass deltaDepth (grayChargeAtRoot i G)).sum := by
  induction I with
  | nil => simp [grayChargeMass, grayMassOfCount]
  | cons i I ih =>
      have hnot : i ∉ I := (List.nodup_cons.mp hI).1
      have htail := ih (List.nodup_cons.mp hI).2
      have hcons : (G.filter fun z => decide (z.1 ∈ i :: I)) =
          G.filter fun z => decide (z.1 = i) || decide (z.1 ∈ I) := by
        apply List.filter_congr
        intro z _
        by_cases h1 : z.1 = i
        · simp [h1]
        · by_cases h2 : z.1 ∈ I <;> simp [h1, h2]
      have hsplit := length_filter_or G
        (fun z => decide (z.1 = i)) (fun z => decide (z.1 ∈ I))
        (fun z _ hzz => hnot (by
          have h1 : z.1 = i := of_decide_eq_true hzz.1
          have h2 : z.1 ∈ I := of_decide_eq_true hzz.2
          exact h1 ▸ h2))
      have hroot : (G.filter fun z => decide (z.1 = i)) =
          grayChargeAtRoot i G := by
        unfold grayChargeAtRoot
        apply List.filter_congr
        intro z _
        by_cases h : z.1 = i
        · simp [h]
        · simp [h]
      rw [List.map_cons, List.sum_cons, ← htail, ← hroot]
      unfold grayChargeMass grayMassOfCount
      rw [hcons, hsplit]
      push_cast
      ring

/-- Day's subfamily clause, extracted. -/
lemma familyGrayChargeAtB.subfamily
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (h : familyGrayChargeAtB eta kappa alpha beta epsDepth deltaDepth n A c s G = true)
    {I : List Nat} (hI : I ∈ (List.range n).sublists) :
    kappa * (2 * totalRootRequestOnList I c - totalRootRequest n c) ≤
      grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈ I)) := by
  unfold familyGrayChargeAtB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 I hI

end Kolmogorov
