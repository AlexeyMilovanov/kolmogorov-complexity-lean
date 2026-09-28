import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderGraft
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRelocation
import KolmogorovMathlib.MonotoneComplexity.GacsDayReserveMass
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCodeStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayBlocking
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable

/-!
# The tail of the gray ladder

This file implements the bounded parallel probe-and-raise loop of SUV
pp. 142--143.  The first ingredient is the source-faithful notion of a
reserved interval.  An allocated cylinder and an epsilon-cylinder only have
to intersect: if the allocated cylinder is coarser, the epsilon-cylinder is
still a part of the space allocated to the vertex.
-/

namespace Kolmogorov

/-- Extend a binary cylinder to the prescribed depth. -/
def extendCylinder (e : ℕ) (c : BitString) : BitString :=
  c ++ List.replicate (e - c.length) false

/-- Extending a string no longer than `e` gives a string of length exactly `e`. -/
lemma length_extendCylinder {e : ℕ} {c : BitString} (hc : c.length ≤ e) :
    (extendCylinder e c).length = e := by
  simp [extendCylinder]
  omega

/-- The extension of a string keeps that string as a prefix. -/
lemma prefix_extendCylinder (e : ℕ) (c : BitString) :
    c <+: extendCylinder e c := by
  simp [extendCylinder]

/-- If `v` is a prefix of `R`, every cylinder comparable with `R` is
comparable with `v`. -/
lemma prefixComparable_of_prefix_of_prefixComparable
    {v R c : BitString} (hvR : v <+: R)
    (hRc : R <+: c ∨ c <+: R) :
    v <+: c ∨ c <+: v := by
  rcases hRc with hRc | hcR
  · exact Or.inl (hvR.trans hRc)
  · rcases List.prefix_or_prefix_of_prefix hcR hvR with hcv | hvc
    · exact Or.inr hcv
    · exact Or.inl hvc

/-- `R` is a source-faithful reserved cylinder for the vertex `x`: `R` has length `e`, it is
prefix-comparable with some string allocated by `m` at `x`, it is comparable with no allocation
of `m` at a `b`-ary vertex incomparable with `x`, and it is comparable with no string of the
standing allocation `A`. -/
def IsTailReserve (e b : ℕ) (A : Allocation) (m : ServerMove)
    (x : GacsDayNode) (R : BitString) : Prop :=
  R.length = e ∧
    (∃ v ∈ getAlloc m x, R <+: v ∨ v <+: R) ∧
    (∀ y, (∀ d ∈ y, d < b) → ¬ (x <+: y ∨ y <+: x) →
      ∀ c ∈ getAlloc m y, ¬ (R <+: c ∨ c <+: R)) ∧
    (∀ a ∈ A, ¬ (R <+: a ∨ a <+: R))

/-- Serving a request of size `2^(-e)` produces a reserved
epsilon-cylinder.  This is the formal version of SUV p. 139, "increase its
request up to epsilon (which creates a reserved interval automatically)". -/
theorem exists_tailReserve_of_serves
    {e b : ℕ} {A : Allocation} {m : ServerMove} {x : GacsDayNode}
    (hcoh : serverMoveCoherent b m)
    (hx : ∀ d ∈ x, d < b)
    (havoid : allocationAvoidsUnavailable A (getAlloc m x))
    (hserve : Serves (getAlloc m x) (dyadicScale e)) :
    ∃ R, IsTailReserve e b A m x R ∧
      ∃ v ∈ getAlloc m x, v <+: R := by
  rcases hserve with ⟨v, hv, hmass⟩
  have hcast : (((dyadicScale e : ℚ) : ℝ)) = (1 / 2 : ℝ) ^ e := by
    simp only [dyadicScale]
    push_cast
    ring
  have hlen : v.length ≤ e := by
    by_contra h
    push_neg at h
    have hstrict : (1 / 2 : ℝ) ^ v.length < (1 / 2 : ℝ) ^ e :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) h
    rw [hcast] at hmass
    linarith
  let R := extendCylinder e v
  have hvR : v <+: R := prefix_extendCylinder e v
  refine ⟨R, ⟨length_extendCylinder hlen,
    ⟨v, hv, Or.inr hvR⟩, ?_, ?_⟩, v, hv, hvR⟩
  · intro y hy hxy c hc hcomp
    have hdisj := disjointAllocations_of_incomparable hcoh
      (not_or.mp hxy).1 (not_or.mp hxy).2 hx hy
    exact hdisj v hv c hc
      (prefixComparable_of_prefix_of_prefixComparable hvR hcomp)
  · intro a ha hcomp
    exact havoid v hv a ha
      (prefixComparable_of_prefix_of_prefixComparable hvR hcomp)

/-- Tail reserves at incomparable vertices are represented by distinct
epsilon-cylinders. -/
theorem IsTailReserve.ne_of_incomparable
    {e b : ℕ} {A : Allocation} {m : ServerMove}
    {x y : GacsDayNode} {R S : BitString}
    (hR : IsTailReserve e b A m x R)
    (hS : IsTailReserve e b A m y S)
    (hx : ∀ d ∈ x, d < b)
    (hxy : ¬ (x <+: y ∨ y <+: x)) : R ≠ S := by
  rintro rfl
  obtain ⟨v, hv, hRv⟩ := hR.2.1
  exact hS.2.2.1 x hx (fun h => hxy h.symm) v hv hRv

/-- A tail reserve in a family also avoids the root allocation of every other
tree. -/
def IsTailFamilyReserve (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) : Prop :=
  IsTailReserve e b A (familyServerMoveAt sm i) x R ∧
    ∀ j, j < n → j ≠ i → ∀ c ∈ getFamilyAlloc sm j [],
      ¬ (R <+: c ∨ c <+: R)

/-- Serving an epsilon request at a legal family vertex creates a family
reserve. -/
theorem exists_tailFamilyReserve_of_serves
    {e b n i T : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {x : GacsDayNode}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n)
    (hx : ∀ d ∈ x, d < b)
    (hserve : Serves (getFamilyAlloc (sm T) i x) (dyadicScale e)) :
    ∃ R, IsTailFamilyReserve e b A n i (sm T) x R := by
  have hcoh := (hsm.1 i hi).1 T
  have havoid := hsm.2.2 T i hi x
  obtain ⟨R, hR, v, hv, hvR⟩ :=
    exists_tailReserve_of_serves hcoh hx havoid hserve
  refine ⟨R, hR, ?_⟩
  intro j hj hji c hc hcomp
  obtain ⟨u, hu, huv⟩ :=
    allocationSubset_getAlloc_root hcoh x hx v hv
  have hroot := hsm.2.1 T i hi j hj (Ne.symm hji)
  apply hroot u hu c hc
  exact prefixComparable_of_prefix_of_prefixComparable
    (huv.trans hvR) hcomp

/-- Family reserves in different trees are distinct. -/
theorem IsTailFamilyReserve.ne_of_ne_tree
    {e b n i j : ℕ} {A : Allocation} {sm : FamilyServerMove}
    {x y : GacsDayNode} {R S : BitString}
    (hcoh : serverMoveCoherent b (familyServerMoveAt sm i))
    (hR : IsTailFamilyReserve e b A n i sm x R)
    (hS : IsTailFamilyReserve e b A n j sm y S)
    (hx : ∀ d ∈ x, d < b) (hi : i < n) (hij : i ≠ j) : R ≠ S := by
  rintro rfl
  obtain ⟨v, hv, hRv⟩ := hR.1.2.1
  obtain ⟨u, hu, huv⟩ := allocationSubset_getAlloc_root hcoh x hx v hv
  apply hS.2 i hi hij u hu
  rcases hRv with hRv | hvR
  · exact List.prefix_or_prefix_of_prefix hRv huv
  · exact Or.inr (huv.trans hvR)

/-- Source-faithful tail reserves contribute their full coarse mass to the
family gray area. -/
theorem familyGrayMass_ge_of_tailFamilyReserves
    {epsDepth deltaDepth n T b : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hcoh : ∀ i, i < n →
      serverMoveCoherent b (familyServerMoveAt (sm T) i))
    {ι : Type*} [Fintype ι]
    (tree : ι → ℕ) (x : ι → GacsDayNode) (R : ι → BitString)
    (htree : ∀ j, tree j < n)
    (hnodes : ∀ j, ∀ d ∈ x j, d < b)
    (hdistinct : ∀ j l, j ≠ l →
      tree j ≠ tree l ∨ ¬ (x j <+: x l ∨ x l <+: x j))
    (hres : ∀ j, IsTailFamilyReserve epsDepth b A n (tree j)
      (sm T) (x j) (R j)) :
    (Fintype.card ι : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      familyGrayMass epsDepth deltaDepth n T A sm := by
  classical
  have hinj : Function.Injective R := by
    intro j l hjl
    by_contra hne
    rcases hdistinct j l hne with htr | hinc
    · exact IsTailFamilyReserve.ne_of_ne_tree
        (hcoh (tree j) (htree j)) (hres j) (hres l)
        (hnodes j) (htree j) htr hjl
    · have hsame : tree j = tree l := by
        by_contra htr
        exact IsTailFamilyReserve.ne_of_ne_tree
          (hcoh (tree j) (htree j)) (hres j) (hres l)
          (hnodes j) (htree j) htr hjl
      have hl := hres l
      rw [← hsame] at hl
      exact (hres j).1.ne_of_incomparable hl.1 (hnodes j) hinc hjl
  set P : Finset BitString := Finset.image R Finset.univ with hP
  have hcard : P.card = Fintype.card ι := by
    rw [hP, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hlen : ∀ p ∈ P, p.length = epsDepth := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.1
  have hnb : ∀ p ∈ P,
      ∃ s ∈ familyAllocated n T sm, p <+: s ∨ s <+: p := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, hRv⟩ := (hres j).1.2.1
    obtain ⟨y, hy, hyv⟩ := allocationSubset_getAlloc_root
      (hcoh (tree j) (htree j)) (x j) (hnodes j) v hv
    refine ⟨y, ?_, ?_⟩
    · refine Finset.mem_biUnion.mpr
        ⟨⟨tree j, htree j⟩, Finset.mem_univ _, ?_⟩
      exact List.mem_toFinset.mpr hy
    · rcases hRv with hRv | hvR
      · exact List.prefix_or_prefix_of_prefix hRv hyv
      · exact Or.inr (hyv.trans hvR)
  have havoid : ∀ p ∈ P, ∀ u ∈ A,
      ¬ (p <+: u ∨ u <+: p) := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.2.2.2
  have hmass := familyGrayMass_ge_of_coarse_cells
    (n := n) (T := T) (A := A) (sm := sm)
    hed P hlen hnb havoid
  rwa [hcard] at hmass

/-! ## A finite reserve test -/

/-- Boolean test for membership in the `b`-ary tree: every digit of `x` is less than `b`. -/
def nodeInTreeB (b : ℕ) (x : GacsDayNode) : Bool :=
  x.all fun d => decide (d < b)

/-- The membership test holds exactly when every entry of the node is below the branching. -/
lemma nodeInTreeB_eq_true_iff (b : ℕ) (x : GacsDayNode) :
    nodeInTreeB b x = true ↔ ∀ d ∈ x, d < b := by
  simp [nodeInTreeB]

/-- Boolean prefix comparability of two game vertices: `x` is a prefix of `y` or `y` is a prefix of
`x`. -/
def nodeComparableB (x y : GacsDayNode) : Bool :=
  x.isPrefixOf y || y.isPrefixOf x

/-- The comparability test on nodes holds exactly when one node is a prefix of the other. -/
lemma nodeComparableB_eq_true_iff (x y : GacsDayNode) :
    nodeComparableB x y = true ↔ x <+: y ∨ y <+: x := by
  simp [nodeComparableB, isPrefixOf_eq_decide]

/-- Boolean same-tree exclusion clause: for every key `p` of the server move `m` that is a `b`-ary
vertex incomparable with `x`, the allocation of `m` at `p` is not comparable with `R`. -/
def tailAvoidsOthersB (b : ℕ) (m : ServerMove)
    (x : GacsDayNode) (R : BitString) : Bool :=
  m.all fun p =>
    if nodeInTreeB b p.1 && !nodeComparableB x p.1 then
      !comparableB (getAlloc m p.1) R
    else true

/-- The avoidance test holds exactly when `R` is incomparable with everything the server has
allocated at nodes incomparable with `x`. -/
lemma tailAvoidsOthersB_eq_true_iff
    (b : ℕ) (m : ServerMove) (x : GacsDayNode) (R : BitString) :
    tailAvoidsOthersB b m x R = true ↔
      ∀ y, (∀ d ∈ y, d < b) → ¬ (x <+: y ∨ y <+: x) →
        ∀ c ∈ getAlloc m y, ¬ (R <+: c ∨ c <+: R) := by
  constructor
  · intro h y hy hxy c hc hcomp
    unfold tailAvoidsOthersB at h
    have hne : getAlloc m y ≠ [] := by
      intro hz
      rw [hz] at hc
      simp at hc
    obtain ⟨p, hp, hp1⟩ := exists_key_of_getAlloc_ne_nil hne
    have hall := (List.all_eq_true.mp h) p hp
    have hguard :
        (nodeInTreeB b p.1 && !nodeComparableB x p.1) = true := by
      rw [Bool.and_eq_true]
      constructor
      · exact (nodeInTreeB_eq_true_iff b p.1).mpr (by simpa [hp1] using hy)
      · have hincp : ¬ (x <+: p.1 ∨ p.1 <+: x) := by
          simpa [hp1] using hxy
        cases hnb : nodeComparableB x p.1 with
        | false => simp
        | true =>
            exact False.elim
              (hincp ((nodeComparableB_eq_true_iff x p.1).mp hnb))
    rw [if_pos hguard, Bool.not_eq_true'] at hall
    apply (comparableB_eq_false_iff _ _).mp hall
    refine ⟨c, ?_, hcomp⟩
    simpa [hp1] using hc
  · intro h
    unfold tailAvoidsOthersB
    apply List.all_eq_true.mpr
    intro p hp
    split
    · rename_i hguard
      rw [Bool.and_eq_true] at hguard
      have hnode : ∀ d ∈ p.1, d < b :=
        nodeInTreeB_eq_true_iff b p.1 |>.mp hguard.1
      have hinc : ¬ (x <+: p.1 ∨ p.1 <+: x) := by
        rw [← nodeComparableB_eq_true_iff]
        have hfalse : nodeComparableB x p.1 = false := by
          simpa using hguard.2
        simp [hfalse]
      rw [Bool.not_eq_true']
      apply (comparableB_eq_false_iff _ _).mpr
      rintro ⟨c, hc, hcomp⟩
      exact h p.1 hnode hinc c hc hcomp
    · rfl

/-- Boolean test for a source-faithful reserve in one tree: `R` has length `e`, is comparable with
the allocation of `m` at `x`, passes `tailAvoidsOthersB b m x R`, and is comparable with no
string of `A`. -/
def tailReserveAtB (e b : ℕ) (A : Allocation) (m : ServerMove)
    (x : GacsDayNode) (R : BitString) : Bool :=
  decide (R.length = e) && comparableB (getAlloc m x) R &&
    tailAvoidsOthersB b m x R && !comparableB A R

/-- The decidable test for a reserve agrees with the predicate. -/
lemma tailReserveAtB_eq_true_iff
    (e b : ℕ) (A : Allocation) (m : ServerMove)
    (x : GacsDayNode) (R : BitString) :
    tailReserveAtB e b A m x R = true ↔
      IsTailReserve e b A m x R := by
  rw [tailReserveAtB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  rw [comparableB_eq_true_iff, tailAvoidsOthersB_eq_true_iff,
    comparableB_eq_false_iff]
  simp only [IsTailReserve, not_exists, not_and, and_assoc]

/-- Boolean family reserve test: `R` passes `tailReserveAtB` for the `i`-th tree of the family move
and is comparable with no root allocation of the other trees `j < n`. -/
def tailFamilyReserveAtB (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) : Bool :=
  tailReserveAtB e b A (familyServerMoveAt sm i) x R &&
    (List.range n).all fun j =>
      if j = i then true else !comparableB (getFamilyAlloc sm j []) R

/-- The decidable test for a family reserve agrees with the predicate. -/
lemma tailFamilyReserveAtB_eq_true_iff
    (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) :
    tailFamilyReserveAtB e b A n i sm x R = true ↔
      IsTailFamilyReserve e b A n i sm x R := by
  rw [tailFamilyReserveAtB, Bool.and_eq_true, tailReserveAtB_eq_true_iff]
  constructor
  · rintro ⟨hR, hall⟩
    refine ⟨hR, ?_⟩
    intro j hj hji c hc hcomp
    have htest := (List.all_eq_true.mp hall) j (by simp [hj])
    rw [if_neg hji] at htest
    rw [Bool.not_eq_true', comparableB_eq_false_iff] at htest
    exact htest ⟨c, hc, hcomp⟩
  · rintro ⟨hR, hcross⟩
    refine ⟨hR, List.all_eq_true.mpr ?_⟩
    intro j hj
    have hjn : j < n := by simpa using List.mem_range.mp hj
    split
    · rfl
    · rename_i hji
      rw [Bool.not_eq_true']
      apply (comparableB_eq_false_iff _ _).mpr
      rintro ⟨c, hc, hcomp⟩
      exact hcross j hjn hji c hc hcomp

/-- The first string of `allStrings e` that passes `tailFamilyReserveAtB e b A n i sm x`, and `none`
if there is none. -/
def getTailFamilyReserve (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) : Option BitString :=
  (allStrings e).find? (tailFamilyReserveAtB e b A n i sm x)

/-- The search returns a family reserve exactly when one exists. -/
lemma getTailFamilyReserve_isSome_iff
    (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) :
    (getTailFamilyReserve e b A n i sm x).isSome ↔
      ∃ R, IsTailFamilyReserve e b A n i sm x R := by
  constructor
  · intro hs
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨R, (tailFamilyReserveAtB_eq_true_iff
      e b A n i sm x R).mp ?_⟩
    exact List.find?_some hR
  · rintro ⟨R, hR⟩
    have hmem : R ∈ allStrings e :=
      (mem_allStrings e R).mpr hR.1.1
    rcases hf : (allStrings e).find?
        (tailFamilyReserveAtB e b A n i sm x) with _ | S
    · have hfalse := List.find?_eq_none.mp hf R hmem
      rw [(tailFamilyReserveAtB_eq_true_iff
        e b A n i sm x R).mpr hR] at hfalse
      contradiction
    · simp [getTailFamilyReserve, hf]

/-! ## The bounded descending scale schedule -/

/-- The number of parallel probe rounds at stage `q`: the deliberately roomy bound `256 * (q + 1) ^
2`. -/
def grayTailRoundCount (q : ℕ) : ℕ := 256 * (q + 1) ^ 2

/-- The number of advantage-phase rounds, `grayTailRoundCount q - 8`: the eight remaining levels of
`grayTailRoundCount` are reserved for the spend phase. -/
def grayChargedAdvantageRoundCount (q : ℕ) : ℕ :=
  grayTailRoundCount q - 8

/-- The advantage round budget is `256 * (q + 1) ^ 2 - 8`. -/
@[simp] lemma grayChargedAdvantageRoundCount_eq (q : ℕ) :
    grayChargedAdvantageRoundCount q = 256 * (q + 1) ^ 2 - 8 := by
  simp [grayChargedAdvantageRoundCount, grayTailRoundCount]

/-- The tail round count leaves room for the eight spend passes. -/
lemma grayTailRoundCount_eight_lt (q : ℕ) :
    8 < grayTailRoundCount q := by
  have hsq : 0 < (q + 1) ^ 2 := by positivity
  simp only [grayTailRoundCount]
  omega

/-- The advantage round budget is positive. -/
lemma grayChargedAdvantageRoundCount_pos (q : ℕ) :
    0 < grayChargedAdvantageRoundCount q := by
  have h := grayTailRoundCount_eight_lt q
  unfold grayChargedAdvantageRoundCount
  omega

/-- The advantage rounds and the eight spend passes together make up the tail round count. -/
@[simp] lemma grayChargedAdvantageRoundCount_add_eight (q : ℕ) :
    grayChargedAdvantageRoundCount q + 8 = grayTailRoundCount q := by
  exact Nat.sub_add_cancel (grayTailRoundCount_eight_lt q).le

/-- The outer branching bound `max 2 (256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)))`.
Keeping the large exponent behind a definition prevents proof elaboration from repeatedly
normalising it. -/
def grayTailBaseBranch (q L : ℕ) : ℕ :=
  max 2 (256 * (q + 1) *
    2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)))

/-- The coarse depth of round `r`: `grayCallDepth q e + (grayTailRoundCount q - 1 - r) * L`. Rounds
run from fine to coarse, so the fine depth of the next round is the coarse depth of the
preceding one. -/
def grayTailRoundEps (q L e r : ℕ) : ℕ :=
  grayCallDepth q e + (grayTailRoundCount q - 1 - r) * L

/-- The fine depth `grayTailRoundEps q L e r + L` of round `r`: its coarse depth plus the rung
width `L`. -/
def grayTailRoundDelta (q L e r : ℕ) : ℕ :=
  grayTailRoundEps q L e r + L

/-- The epsilon depth of a round is at most its delta depth. -/
lemma grayTailRoundEps_le_delta (q L e r : ℕ) :
    grayTailRoundEps q L e r ≤ grayTailRoundDelta q L e r :=
  Nat.le_add_right _ _

/-- Inside the round budget, the delta depth of a round is the epsilon depth of the round before
it. -/
lemma grayTailRoundDelta_succ
    {q L e r : ℕ} (hr : r + 1 < grayTailRoundCount q) :
    grayTailRoundDelta q L e (r + 1) = grayTailRoundEps q L e r := by
  have hcoeff :
      (grayTailRoundCount q - 1 - (r + 1)).succ =
        grayTailRoundCount q - 1 - r := by
    omega
  simp only [grayTailRoundDelta, grayTailRoundEps]
  rw [Nat.add_assoc, ← Nat.succ_mul, hcoeff]

/-- The epsilon depth of a round is at least the call depth `grayCallDepth q e`. -/
lemma grayTailRoundEps_lower (q L e r : ℕ) :
    grayCallDepth q e ≤ grayTailRoundEps q L e r :=
  Nat.le_add_right _ _

/-- The epsilon depth of a round stays below `e + (256 * (q + 1) ^ 2 - 1) * L + 3 * q + 7`. -/
lemma grayTailRoundEps_upper (q L e r : ℕ) :
    grayTailRoundEps q L e r ≤
      e + (256 * (q + 1) ^ 2 - 1) * L + 3 * q + 7 := by
  have hc := grayCallDepth_le q e
  have hs : grayTailRoundCount q - 1 - r ≤ grayTailRoundCount q - 1 :=
    Nat.sub_le _ _
  have hm := Nat.mul_le_mul_right L hs
  simp only [grayTailRoundEps, grayTailRoundCount] at hm ⊢
  omega

/-- The delta depth of a round stays below `e + 256 * (q + 1) ^ 2 * L + 256 * (q + 1)`. -/
lemma grayTailRoundDelta_upper (q L e r : ℕ) :
    grayTailRoundDelta q L e r ≤
      e + 256 * (q + 1) ^ 2 * L + 256 * (q + 1) := by
  have he := grayTailRoundEps_upper q L e r
  have hq1 : 1 ≤ q + 1 := by omega
  have hsq : 1 ≤ (q + 1) ^ 2 := by
    simp [pow_two]
  have hL : L ≤ (q + 1) ^ 2 * L := by
    simpa using Nat.mul_le_mul_right L hsq
  have hN : 1 ≤ 256 * (q + 1) ^ 2 := by omega
  have hmain :
      (256 * (q + 1) ^ 2 - 1) * L + L ≤
        256 * (q + 1) ^ 2 * L := by
    calc
      _ = ((256 * (q + 1) ^ 2 - 1) + 1) * L := by
        rw [Nat.add_mul, one_mul]
      _ ≤ _ := by
        rw [Nat.sub_add_cancel hN]
  have hlin : 3 * q + 7 ≤ 256 * (q + 1) := by omega
  simp only [grayTailRoundDelta]
  omega

/-- The epsilon depth of a round exceeds the call depth by at most
`(256 * (q + 1) ^ 2 - 1) * L`. -/
lemma grayTailRoundEps_sub_call_le (q L e r : ℕ) :
    grayTailRoundEps q L e r - grayCallDepth q e ≤
      (256 * (q + 1) ^ 2 - 1) * L := by
  simp only [grayTailRoundEps, grayTailRoundCount, Nat.add_sub_cancel_left]
  exact Nat.mul_le_mul_right L
    (Nat.sub_le _ _)

/-- The tail rounds fit inside the base branching `grayTailBaseBranch q L`. -/
lemma grayTailRoundCount_le_linear_bound (q L : ℕ) :
    grayTailRoundCount q ≤ grayTailBaseBranch q L := by
  let E := 256 * (q + 1) ^ 2 * L + 256 * (q + 1)
  have hq := Nat.le_two_pow_self (q + 1)
  have hsq :
      (q + 1) ^ 2 ≤ (2 ^ (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left hq 2
  have hJ :
      grayTailRoundCount q ≤ 2 ^ (2 * (q + 1) + 8) := by
    calc
      grayTailRoundCount q = 256 * (q + 1) ^ 2 := rfl
      _ ≤ 256 * (q + 1) ^ 2 := by
        have hq1 : 1 ≤ q + 1 := by omega
        have hq : 1 ≤ (q + 1) ^ 2 := by
          simp [pow_two]
        nlinarith
      _ ≤ 256 * (2 ^ (q + 1)) ^ 2 :=
        Nat.mul_le_mul_left 256 hsq
      _ = 2 ^ (2 * (q + 1) + 8) := by
        rw [show 256 = 2 ^ 8 by norm_num, pow_two,
          ← pow_add, ← pow_add]
        (congr 1; omega)
  have he : 2 * (q + 1) + 8 ≤ E := by
    dsimp [E]
    omega
  have hpow : grayTailRoundCount q ≤ 2 ^ E :=
    le_trans hJ (Nat.pow_le_pow_right (by omega) he)
  have hcoef : 1 ≤ 256 * (q + 1) := by omega
  have hmul : 2 ^ E ≤ 256 * (q + 1) * 2 ^ E := by
    simpa using Nat.mul_le_mul_right (2 ^ E) hcoef
  unfold grayTailBaseBranch
  exact le_trans hpow (le_trans hmul (le_max_right _ _))

/-- The branching a recursive call of a round needs fits inside the base branching. -/
lemma grayTailRecursiveBranch_le
    {q L B e r : ℕ}
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L)) :
    ladderBranching B (grayCallDepth q e) (grayTailRoundEps q L e r) ≤
      grayTailBaseBranch q L := by
  let E := 256 * (q + 1) ^ 2 * L + 256 * (q + 1)
  let K := 256 * (q + 1) * 2 ^ E
  have hsub := grayTailRoundEps_sub_call_le q L e r
  have hexp : (256 * (q + 1) ^ 2 - 1) * L ≤ E := by
    dsimp [E]
    have hcoeff : 256 * (q + 1) ^ 2 - 1 ≤ 256 * (q + 1) ^ 2 :=
      Nat.sub_le _ _
    exact le_trans (Nat.mul_le_mul_right L hcoeff) (Nat.le_add_right _ _)
  have hpow : 2 ^ (grayTailRoundEps q L e r - grayCallDepth q e) ≤
      2 ^ E :=
    Nat.pow_le_pow_right (by omega) (le_trans hsub hexp)
  have hcoef : 1 ≤ 256 * (q + 1) := by omega
  have hcoef2 : 2 ≤ 256 * (q + 1) := by omega
  have hpowK : 2 * 2 ^ (grayTailRoundEps q L e r - grayCallDepth q e) ≤ K := by
    dsimp [K]
    exact Nat.mul_le_mul hcoef2 hpow
  have hL : L ≤ E := by
    dsimp [E]
    have hq1 : 1 ≤ q + 1 := by omega
    have hsq : 1 ≤ (q + 1) ^ 2 := by
      simp [pow_two]
    have hc : 1 ≤ 256 * (q + 1) ^ 2 := by
      simpa using Nat.mul_le_mul (by omega : 1 ≤ 256) hsq
    exact le_trans
      (by simpa using Nat.mul_le_mul_right L hc)
      (Nat.le_add_right _ _)
  have hinner : 256 * (q + 1) * 2 ^ L ≤ K := by
    dsimp [K]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hL)
  have hBK : B ≤ max 2 K :=
    le_trans hB (max_le_max le_rfl hinner)
  unfold ladderBranching grayTailBaseBranch
  exact max_le
    (le_trans hpowK (le_max_right _ _))
    hBK

/-! ## Coarse stopping tests

The recursive rung is specified at an a priori unknown fine depth.  In the
parallel construction all unavailable cylinders are truncated at the coarse
depth.  Refinement then merely splits every coarse gray cell into all of its
descendants, so its measure is exactly unchanged.
-/

/-- When the unavailable strings are no longer than `epsDepth`, refining the gray area from
`epsDepth` to `deltaDepth` does not change its mass. -/
lemma grayMass_eq_at_coarse_depth
    {epsDepth deltaDepth : ℕ} (hed : epsDepth ≤ deltaDepth)
    {allocated unavailable : Finset BitString}
    (hu : ∀ c ∈ unavailable, c.length ≤ epsDepth) :
    ((newGrayCells epsDepth deltaDepth allocated unavailable).card : ℚ) *
        (1 / 2 : ℚ) ^ deltaDepth =
      ((newGrayCells epsDepth epsDepth allocated unavailable).card : ℚ) *
        (1 / 2 : ℚ) ^ epsDepth := by
  have hd := card_newGrayCells_of_refine
    (allocated := allocated) (unavailable := unavailable) hed hu
  have he := card_newGrayCells_of_refine
    (allocated := allocated) (unavailable := unavailable) (le_refl epsDepth) hu
  have he' :
      (newGrayCells epsDepth epsDepth allocated unavailable).card =
        ((neighborhoodCells epsDepth allocated) \
          (neighborhoodCells epsDepth unavailable)).card := by
    simpa using he
  rw [hd, he']
  push_cast
  rw [mul_assoc, two_pow_sub_mul_half_pow hed]

/-- When the unavailable allocation is no longer than `epsDepth`, the gray mass of a family play
does not depend on the finer depth. -/
lemma familyGrayMass_eq_at_coarse_depth
    {epsDepth deltaDepth n T : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} (hA : ∀ c ∈ A, c.length ≤ epsDepth)
    (sm : ℕ → FamilyServerMove) :
    familyGrayMass epsDepth deltaDepth n T A sm =
      familyGrayMass epsDepth epsDepth n T A sm := by
  unfold familyGrayMass
  apply grayMass_eq_at_coarse_depth hed
  simpa using hA

/-- When the unavailable allocation is no longer than `epsDepth`, a gray goal at the finer depth
already holds at the coarse depth. -/
lemma familyGrayGoal_at_coarse_depth
    {kappa beta : ℚ} {epsDepth deltaDepth n : ℕ}
    (hed : epsDepth ≤ deltaDepth) {A : Allocation}
    (hA : ∀ c ∈ A, c.length ≤ epsDepth)
    {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (H : familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm) :
    familyGrayGoal kappa beta epsDepth epsDepth n A cm sm := by
  obtain ⟨T, hbeta, hkappa, hprogress⟩ := H
  have hmass := familyGrayMass_eq_at_coarse_depth
    (n := n) (T := T) hed hA sm
  rw [hmass] at hbeta hkappa
  exact ⟨T, hbeta, hkappa, hprogress⟩

/-! ## Stopping and final-adjustment arithmetic -/

/-- The hereditary version of the last-call estimate.  Here `gamma` is the
sum of all non-last recursive requests and `last` is the one discarded
component.  The finer call window makes the reserve term leave a uniform
positive margin even though the hereditary certificate charges the discarded
component once more in its ambient-family term. -/
lemma grayTail_robust_lastCall_accounting
    {kappa eps gamma last : ℚ}
    (hk : 1 ≤ kappa) (heps : 0 ≤ eps) (_hgamma : 0 ≤ gamma)
    (hgamma_cap : gamma ≤ eps) (hlast : 0 ≤ last)
    (hlast_cap : last ≤ eps / (12 * kappa)) :
    (kappa + 1 / 2) * (gamma + last) ≤
      kappa * (gamma - last) + (3 / 4 : ℚ) * eps := by
  have hden : (0 : ℚ) < 12 * kappa := by positivity
  have hlast_mul : 12 * kappa * last ≤ eps := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ hden).mp hlast_cap
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) hlast,
    mul_nonneg (sub_nonneg.mpr hk) heps]

/-- The threshold branch also survives discarding its last recursive
component. If the full accumulated request has crossed
`epsilon - epsilon / (6 * kappa)`, the last component is at most
`epsilon / (12 * kappa)`, and a fresh reserve contributes `epsilon`, then
the displayed request may safely be raised all the way to `epsilon`. -/
lemma grayTail_robust_threshold_lastCall_accounting
    {kappa eps before last : ℚ}
    (hk : 1 ≤ kappa) (heps : 0 ≤ eps)
    (_hbefore : 0 ≤ before) (_hlast : 0 ≤ last)
    (hthreshold :
      eps - eps / (6 * kappa) ≤ before + last)
    (hlast_cap : last ≤ eps / (12 * kappa)) :
    (kappa + 1 / 2) * eps ≤
      kappa * (before - last) + eps := by
  have hkpos : (0 : ℚ) < kappa := lt_of_lt_of_le one_pos hk
  have hden : (0 : ℚ) < 12 * kappa := by positivity
  have hlast_mul : 12 * kappa * last ≤ eps := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ hden).mp hlast_cap
  have hthreshold_mul :=
    mul_le_mul_of_nonneg_left hthreshold hkpos.le
  have hcancel : kappa * (eps / (6 * kappa)) = eps / 6 := by
    field_simp
  rw [mul_sub, hcancel] at hthreshold_mul
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) heps,
    mul_nonneg hkpos.le _hbefore, mul_nonneg hkpos.le _hlast]

/-- If the final recursive call is discarded from the gray sum, one fresh
reserve still pays for both that call and the extra half-unit of amplification.
The call cap is the right endpoint of the source window
`q ≤ epsilon / (6 * kappa)`. -/
lemma grayTail_lastCall_accounting {kappa eps gamma q : ℚ}
    (hk : 1 ≤ kappa) (heps : 0 ≤ eps) (_hgamma : 0 ≤ gamma)
    (hgamma_cap : gamma ≤ eps) (hq : 0 ≤ q)
    (hq_cap : q ≤ eps / (6 * kappa)) :
    (kappa + 1 / 2) * (gamma + q) ≤ kappa * gamma + eps := by
  have hden : (0 : ℚ) < 6 * kappa := by positivity
  have hqmul : 6 * kappa * q ≤ eps := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ hden).mp hq_cap
  have hlast : (kappa + 1 / 2) * q ≤ eps / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hq]
  nlinarith

/-- Once a son's accumulated request crosses the source threshold, raising it
to `epsilon` is paid for by its fresh reserve. -/
lemma grayTail_threshold_accounting {kappa eps gamma : ℚ}
    (hk : 1 ≤ kappa) (heps : 0 ≤ eps)
    (hgamma : eps - eps / (6 * kappa) ≤ gamma) :
    (kappa + 1 / 2) * eps ≤ kappa * gamma + eps := by
  have hkpos : (0 : ℚ) < kappa := lt_of_lt_of_le one_pos hk
  have hmul := mul_le_mul_of_nonneg_left hgamma (le_of_lt hkpos)
  have hcancel : kappa * (eps / (6 * kappa)) = eps / 6 := by
    field_simp
  rw [mul_sub, hcancel] at hmul
  nlinarith

/-- The final root adjustment of SUV p. 143.  Raising the actual root request
to the target floor preserves the cap and both gray-goal inequalities whenever
the available gray mass already covers the old amplified request and the target
mass. -/
lemma grayTail_adjustedRoot
    {kappa eps gamma mass : ℚ}
    (hk : 1 ≤ kappa) (heps : 0 ≤ eps) (hgamma : 0 ≤ gamma)
    (hgamma_cap : gamma ≤ eps)
    (hmass_gamma : kappa * gamma ≤ mass)
    (hmass_target : (3 / 4 : ℚ) * eps ≤ mass) :
    let rho := max gamma (((3 / 4 : ℚ) * eps) / kappa)
    0 ≤ rho ∧ rho ≤ eps ∧ kappa * rho ≤ mass ∧
      (3 / 4 : ℚ) * eps ≤ kappa * rho := by
  dsimp
  have hkpos : (0 : ℚ) < kappa := lt_of_lt_of_le one_pos hk
  have hfloor0 : 0 ≤ ((3 / 4 : ℚ) * eps) / kappa := by positivity
  have hfloor_cap : ((3 / 4 : ℚ) * eps) / kappa ≤ eps := by
    rw [div_le_iff₀ hkpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) heps]
  have hcancel :
      kappa * (((3 / 4 : ℚ) * eps) / kappa) = (3 / 4 : ℚ) * eps := by
    field_simp
  by_cases h : gamma ≤ ((3 / 4 : ℚ) * eps) / kappa
  · rw [max_eq_right h]
    exact ⟨hfloor0, hfloor_cap, by simpa [hcancel] using hmass_target,
      le_of_eq hcancel.symm⟩
  · have h' : ((3 / 4 : ℚ) * eps) / kappa ≤ gamma := le_of_not_ge h
    rw [max_eq_left h']
    refine ⟨hgamma, hgamma_cap, hmass_gamma, ?_⟩
    calc
      (3 / 4 : ℚ) * eps =
          kappa * (((3 / 4 : ℚ) * eps) / kappa) := hcancel.symm
      _ ≤ kappa * gamma := mul_le_mul_of_nonneg_left h' (le_of_lt hkpos)

/-! ## Freshness of a newly appearing reserve

The source uses one temporal fact which is easy to miss in the static reserve
predicate. If an epsilon-cylinder is a reserve at a later time but was not a
reserve before the last recursive call, then it contained no allocation from
that call's subtree at the earlier time. Otherwise coherence would already
have propagated an anchor to the parent, while monotonicity of the server play
would make all exclusion clauses valid at the earlier time.
-/

/-- Allocation at a descendant is covered by allocation at an ancestor. -/
lemma allocationSubset_getAlloc_of_prefix
    {b : ℕ} {m : ServerMove} (hcoh : serverMoveCoherent b m)
    {x y : GacsDayNode} (hxy : x <+: y)
    (hy : ∀ d ∈ y, d < b) :
    allocationSubset (getAlloc m y) (getAlloc m x) := by
  obtain ⟨z, rfl⟩ := hxy
  induction z generalizing x with
  | nil =>
      simpa using allocationSubset_refl (getAlloc m x)
  | cons d z ih =>
      have hd : d < b := hy d (by simp)
      have htail :
          allocationSubset (getAlloc m (x ++ d :: z))
            (getAlloc m (x ++ [d])) := by
        have hrange : ∀ q ∈ (x ++ [d]) ++ z, q < b := by
          intro q hq
          exact hy q (by simpa [List.append_assoc] using hq)
        simpa [List.append_assoc] using
          (ih (x := x ++ [d]) hrange)
      have hhead :
          allocationSubset (getAlloc m (x ++ [d])) (getAlloc m x) :=
        hcoh.1 x ⟨d, hd⟩
      exact allocationSubset_trans htail hhead

/-- If R first becomes a reserve after time t, then at time t it is
incomparable with every cylinder allocated in the subtree of its owner. -/
theorem IsTailReserve.fresh_of_not_before
    {e b t T : ℕ} {A : Allocation} {sm : ℕ → ServerMove}
    (hsm : serverPlayLegal b sm) (htT : t ≤ T)
    {x : GacsDayNode} (_hx : ∀ d ∈ x, d < b)
    {R : BitString} (hR : IsTailReserve e b A (sm T) x R)
    (hnot : ¬ IsTailReserve e b A (sm t) x R)
    {y : GacsDayNode} (hxy : x <+: y)
    (hy : ∀ d ∈ y, d < b) {c : BitString}
    (hc : c ∈ getAlloc (sm t) y) :
    ¬ (R <+: c ∨ c <+: R) := by
  intro hRc
  have hsub :=
    allocationSubset_getAlloc_of_prefix (hsm.1 t) hxy hy
  obtain ⟨u, hu, huc⟩ := hsub c hc
  have hRu : R <+: u ∨ u <+: R := by
    rcases hRc with hRc | hcR
    · exact List.prefix_or_prefix_of_prefix hRc huc
    · exact Or.inr (huc.trans hcR)
  apply hnot
  refine ⟨hR.1, ⟨u, hu, hRu⟩, ?_, hR.2.2.2⟩
  intro z hz hzx d hd hRd
  have htime := allocationSubset_mono_time hsm htT z
  obtain ⟨d', hd', hd'd⟩ := htime d hd
  apply hR.2.2.1 z hz hzx d' hd'
  rcases hRd with hRd | hdR
  · exact List.prefix_or_prefix_of_prefix hRd hd'd
  · exact Or.inr (hd'd.trans hdR)

end Kolmogorov
