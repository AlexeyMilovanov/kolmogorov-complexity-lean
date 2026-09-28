import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import Mathlib.Data.List.Sublists

/-!
# The hereditary family invariant in Day's induction

The aggregate gray goal is enough at the public boundary, but it is not closed
under the recursive step: the final call belonging to each newly reserved son
has to be discarded. Definition 4.3.2(c) in Day's proof therefore records a
lower bound for every subfamily. This file gives that invariant an executable
form. We use lists of component indices because the controller already stores
families as lists and `List.powerset (List.range n)` is a canonical finite
enumeration of all subfamilies.
-/

namespace Kolmogorov

open scoped BigOperators

/-- Root allocations belonging to the listed family components. -/
def familyAllocatedOnList (indices : List Nat) (s : FamilyServerMove) :
    List BitString :=
  indices.flatMap fun i => getFamilyAlloc s i []

/-- Root request carried by the listed family components. -/
def totalRootRequestOnList (indices : List Nat) (c : FamilyClientMove) : ℚ :=
  indices.foldr (fun i acc => getFamilyReq c i [] + acc) 0

/-- Day's hereditary inequality at one fixed time for the subfamily `indices`: decides `kappa * (2 *
totalRootRequestOnList indices c - totalRootRequest n c) ≤ g`, where `g` is the gray mass
created between `epsDepth` and `deltaDepth` by the root allocations of the listed components
over `A`. -/
def familySubfamilyGrayAtB (kappa : ℚ) (epsDepth deltaDepth n : Nat)
    (A : Allocation) (c : FamilyClientMove) (s : FamilyServerMove)
    (indices : List Nat) : Bool :=
  let g := grayMassOfCount deltaDepth
    (newGrayCount epsDepth deltaDepth (familyAllocatedOnList indices s) A)
  decide (kappa *
    (2 * totalRootRequestOnList indices c - totalRootRequest n c) ≤ g)

/-- The gray mass belonging to one component of the family. Family components
have disjoint root allocations, so this is the local quantity which is stable
under the parallel half-step. -/
def familyComponentGrayMassAtB (epsDepth deltaDepth : Nat) (A : Allocation)
    (s : FamilyServerMove) (i : Nat) : ℚ :=
  grayMassOfCount deltaDepth
    (newGrayCount epsDepth deltaDepth (getFamilyAlloc s i []) A)

/-- The componentwise request-window certificate: every component `i < n` satisfies `beta ≤ kappa *
getFamilyReq c i []` and `getFamilyReq c i [] ≤ (4 / 3) * beta`. It constrains only the root
requests; gray-mass payment is left to the hereditary certificate. -/
def familyPointwiseGrayAtB (kappa beta : ℚ) (_epsDepth _deltaDepth n : Nat)
    (_A : Allocation) (c : FamilyClientMove) (_s : FamilyServerMove) : Bool :=
  (List.range n).all fun i =>
    decide (beta ≤ kappa * getFamilyReq c i []) &&
      decide (getFamilyReq c i [] ≤ (4 / 3 : ℚ) * beta)

/-- The executable strong gray certificate: the aggregate test `familyGrayGoalAtB` on the
allocations of all `n` components, together with `familySubfamilyGrayAtB` for every sublist of
`List.range n` and the request window `familyPointwiseGrayAtB`. -/
def familyRobustGrayGoalAtB (kappa beta : ℚ) (epsDepth deltaDepth n : Nat)
    (A : Allocation) (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyGrayGoalAtB kappa beta epsDepth deltaDepth n A c
      (familyAllocatedOnList (List.range n) s) &&
    ((List.range n).sublists.all
        (familySubfamilyGrayAtB kappa epsDepth deltaDepth n A c s) &&
      familyPointwiseGrayAtB kappa beta epsDepth deltaDepth n A c s)

/-- The hereditary gray alternative of a family game: at some time `T` the certificate
`familyRobustGrayGoalAtB` holds of the client move `cm T` and the server move `sm T`. -/
def familyRobustGrayGoal (kappa beta : ℚ) (epsDepth deltaDepth n : Nat)
    (A : Allocation) (cm : Nat → FamilyClientMove)
    (sm : Nat → FamilyServerMove) : Prop :=
  ∃ T, familyRobustGrayGoalAtB kappa beta epsDepth deltaDepth n A
    (cm T) (sm T) = true

/-- Collecting the allocations of the first `n` clients gives the whole allocated list. -/
@[simp] lemma familyAllocatedOnList_range (n T : Nat)
    (sm : Nat → FamilyServerMove) :
    familyAllocatedOnList (List.range n) (sm T) = familyAllocatedList n T sm := by
  rfl

/-- A round meeting the robust gray goal meets the plain gray goal. -/
lemma familyRobustGrayGoalAtB.to_familyGrayGoalAtB
    {kappa beta : ℚ} {epsDepth deltaDepth n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : familyRobustGrayGoalAtB kappa beta epsDepth deltaDepth n A c s = true) :
    familyGrayGoalAtB kappa beta epsDepth deltaDepth n A c
      (familyAllocatedOnList (List.range n) s) = true := by
  unfold familyRobustGrayGoalAtB at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- A round meeting the robust gray goal meets the pointwise gray goal. -/
lemma familyRobustGrayGoalAtB.to_pointwise
    {kappa beta : ℚ} {epsDepth deltaDepth n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : familyRobustGrayGoalAtB kappa beta epsDepth deltaDepth n A c s = true) :
    familyPointwiseGrayAtB kappa beta epsDepth deltaDepth n A c s = true := by
  unfold familyRobustGrayGoalAtB at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2

/-- Under the pointwise gray goal, each client requests between `beta / kappa` and
`(4/3) * beta` at its root. -/
lemma familyPointwiseGrayAtB.component
    {kappa beta : ℚ} {epsDepth deltaDepth n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : familyPointwiseGrayAtB kappa beta epsDepth deltaDepth n A c s = true)
    {i : Nat} (hi : i < n) :
    beta ≤ kappa * getFamilyReq c i [] ∧
      getFamilyReq c i [] ≤ (4 / 3 : ℚ) * beta := by
  unfold familyPointwiseGrayAtB at h
  rw [List.all_eq_true] at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using
    h i (List.mem_range.mpr hi)

/-- A play meeting the robust gray goal meets the plain gray goal. -/
lemma familyRobustGrayGoal.to_familyGrayGoal
    {kappa beta : ℚ} {epsDepth deltaDepth n : Nat} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {cm : Nat → FamilyClientMove}
    {sm : Nat → FamilyServerMove}
    (h : familyRobustGrayGoal kappa beta epsDepth deltaDepth n A cm sm) :
    familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm := by
  obtain ⟨T, hT⟩ := h
  apply (familyGrayGoal_iff_exists_familyGrayGoalAtB hed n A cm sm).2
  refine ⟨T, ?_⟩
  simpa using familyRobustGrayGoalAtB.to_familyGrayGoalAtB hT

/-- A family game specification carrying the hereditary alternative: the plain `GrayFamilyGameSpec`
for the same parameters, and, against every legal server play, the client either wins by an
unserved positive request or the play satisfies `familyRobustGrayGoal`. -/
structure RobustGrayFamilyGameSpec (kappa alpha beta : ℚ)
    (epsDepth deltaDepth h b n : Nat) (A : Allocation)
    (sigma : ClientFamilyStrategy) : Prop where
  weak : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A sigma
  wins_robust : ∀ sm, familyServerPlayLegal n b A sm →
    familyClientWinsUnservedPositive n h b
        (playClientFamily A n sigma sm) sm ∨
      familyRobustGrayGoal kappa beta epsDepth deltaDepth n A
        (playClientFamily A n sigma sm) sm

end Kolmogorov
