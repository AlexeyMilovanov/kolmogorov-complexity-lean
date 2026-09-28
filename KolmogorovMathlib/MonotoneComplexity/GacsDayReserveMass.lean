import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayWitness

/-!
# Reserved intervals are gray mass

A *reserved interval* for a son `x` at scale `epsilon` (SUV p. 140) is a
cylinder `R` of measure `epsilon` that already contains allocated space of `x`,
meets neither the unavailable set nor the allocation of any vertex outside the
subtree of `x`. `hasReserve` (in `GacsDayLadderStep`) is the predicate; this
file proves the quantitative statement the half-step needs about it:

* `IsReserve` unbundles `hasReserve`, so that a *choice* of reserve can be
  carried around;
* `IsReserve.ne_of_incomparable`: two incomparable sons never share a reserved
  interval -- the reserve of one is anchored in an allocation the reserve of the
  other has to avoid;
* `familyGrayMass_ge_of_reserves`: consequently, `m` sons with reserved
  intervals force at least `m * epsilon` of new gray mass, at any fine scale
  `delta`.

The last statement is the form in which reserved mass enters the accounting of
p. 143: it is the `m * epsilon` cap that `halfStep_accounting` consumes.
-/

namespace Kolmogorov

/-- The unbundled reserve predicate: `R` *is* a reserved interval for `x`. -/
def IsReserve (e : ℕ) (A : Allocation) (m : ServerMove) (x : GacsDayNode) (R : BitString) :
    Prop :=
  R.length = e ∧
    (∃ v ∈ getAlloc m x, R <+: v) ∧
    (∀ y, ¬ (x <+: y ∨ y <+: x) → ∀ c ∈ getAlloc m y, ¬ (R <+: c ∨ c <+: R)) ∧
    (∀ a ∈ A, ¬ (R <+: a ∨ a <+: R))

/-- A node has a reserve exactly when some string is a reserve for it. -/
lemma hasReserve_iff_exists_isReserve {e : ℕ} {A : Allocation} {m : ServerMove}
    {x : GacsDayNode} :
    hasReserve e A m x ↔ ∃ R, IsReserve e A m x R := Iff.rfl

/-- Two incomparable vertices cannot share a reserved interval: the reserve of
one covers allocated space of that vertex, which the reserve of the other is
required to avoid. -/
theorem IsReserve.ne_of_incomparable {e : ℕ} {A : Allocation} {m : ServerMove}
    {x y : GacsDayNode} {R S : BitString}
    (hR : IsReserve e A m x R) (hS : IsReserve e A m y S)
    (hxy : ¬ (x <+: y ∨ y <+: x)) : R ≠ S := by
  rintro rfl
  obtain ⟨v, hv, hRv⟩ := hR.2.1
  exact hS.2.2.1 x (fun h => hxy (h.symm)) v hv (Or.inl hRv)

/-- Along a branch all allocations sit below the root allocation. -/
theorem allocationSubset_getAlloc_root {b : ℕ} {m : ServerMove}
    (hcoh : serverMoveCoherent b m) (x : GacsDayNode) (hx : ∀ c ∈ x, c < b) :
    allocationSubset (getAlloc m x) (getAlloc m []) := by
  induction x using List.reverseRecOn with
  | nil => exact allocationSubset_refl _
  | append_singleton y c ih =>
    have hcb : c < b := hx c (by simp)
    have hy : ∀ d ∈ y, d < b := fun d hd => hx d (by simp [hd])
    exact allocationSubset_trans (hcoh.1 y ⟨c, hcb⟩) (ih hy)

/-- **Reserved intervals are new gray mass.** If finitely many pairwise
incomparable vertices of the `i`-th tree each own a reserved interval at the
coarse scale `epsDepth`, then the gray mass of the family play at any finer
scale `deltaDepth` is at least the total mass of those intervals. -/
theorem familyGrayMass_ge_of_reserves
    {epsDepth deltaDepth n T i b : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hcoh : serverMoveCoherent b (familyServerMoveAt (sm T) i)) (hi : i < n)
    {ι : Type*} [Fintype ι]
    (x : ι → GacsDayNode) (R : ι → BitString)
    (hnodes : ∀ j, ∀ c ∈ x j, c < b)
    (hincomp : ∀ j l, j ≠ l → ¬ (x j <+: x l ∨ x l <+: x j))
    (hres : ∀ j, IsReserve epsDepth A (familyServerMoveAt (sm T) i) (x j) (R j)) :
    (Fintype.card ι : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      familyGrayMass epsDepth deltaDepth n T A sm := by
  classical
  have hinj : Function.Injective R := by
    intro j l hjl
    by_contra hne
    exact (hres j).ne_of_incomparable (hres l) (hincomp j l hne) hjl
  set P : Finset BitString := Finset.image R Finset.univ with hP
  have hcard : P.card = Fintype.card ι := by
    rw [hP, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hlen : ∀ p ∈ P, p.length = epsDepth := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1
  have hnb : ∀ p ∈ P, ∃ s ∈ familyAllocated n T sm, p <+: s ∨ s <+: p := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, hRv⟩ := (hres j).2.1
    obtain ⟨y, hy, hyv⟩ := allocationSubset_getAlloc_root hcoh (x j) (hnodes j) v hv
    refine ⟨y, ?_, List.prefix_or_prefix_of_prefix hRv hyv⟩
    refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    exact List.mem_toFinset.mpr hy
  have havoid : ∀ p ∈ P, ∀ u ∈ A, ¬ (p <+: u ∨ u <+: p) := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).2.2.2
  have hmass := familyGrayMass_ge_of_coarse_cells (n := n) (T := T) (A := A) (sm := sm)
    hed P hlen hnb havoid
  rwa [hcard] at hmass

/-! ### Reserves across the whole family -/

/-- A reserved interval in a *family* play: besides being a reserve inside its
own tree, it must avoid the root allocation of every other tree. Vertices of
another tree are outside the subtree of `x`, so this is the family reading of
the requirement of SUV p. 140. -/
def IsFamilyReserve (e : ℕ) (A : Allocation) (n i : ℕ) (sm : FamilyServerMove)
    (x : GacsDayNode) (R : BitString) : Prop :=
  IsReserve e A (familyServerMoveAt sm i) x R ∧
    ∀ j, j < n → j ≠ i → ∀ c ∈ getFamilyAlloc sm j [], ¬ (R <+: c ∨ c <+: R)

/-- Reserved intervals of vertices living in different trees are distinct. -/
theorem IsFamilyReserve.ne_of_ne_tree {e n i i' b : ℕ} {A : Allocation}
    {sm : FamilyServerMove} {x x' : GacsDayNode} {R R' : BitString}
    (hcoh : serverMoveCoherent b (familyServerMoveAt sm i))
    (hR : IsFamilyReserve e A n i sm x R) (hR' : IsFamilyReserve e A n i' sm x' R')
    (hx : ∀ c ∈ x, c < b) (hi : i < n) (hii : i ≠ i') : R ≠ R' := by
  rintro rfl
  obtain ⟨v, hv, hRv⟩ := hR.1.2.1
  obtain ⟨u, hu, huv⟩ := allocationSubset_getAlloc_root hcoh x hx v hv
  exact hR'.2 i hi hii u hu (List.prefix_or_prefix_of_prefix hRv huv)

/-- **Reserved intervals are new gray mass, family form.** Finitely many
reserved intervals, held by vertices that are either in different trees or
incomparable inside one tree, force at least their total mass of new gray mass
at any finer scale. -/
theorem familyGrayMass_ge_of_familyReserves
    {epsDepth deltaDepth n T b : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hcoh : ∀ i, i < n → serverMoveCoherent b (familyServerMoveAt (sm T) i))
    {ι : Type*} [Fintype ι]
    (tree : ι → ℕ) (x : ι → GacsDayNode) (R : ι → BitString)
    (htree : ∀ j, tree j < n)
    (hnodes : ∀ j, ∀ c ∈ x j, c < b)
    (hdistinct : ∀ j l, j ≠ l → tree j ≠ tree l ∨ ¬ (x j <+: x l ∨ x l <+: x j))
    (hres : ∀ j, IsFamilyReserve epsDepth A n (tree j) (sm T) (x j) (R j)) :
    (Fintype.card ι : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      familyGrayMass epsDepth deltaDepth n T A sm := by
  classical
  have hinj : Function.Injective R := by
    intro j l hjl
    by_contra hne
    rcases hdistinct j l hne with htr | hinc
    · exact IsFamilyReserve.ne_of_ne_tree (hcoh (tree j) (htree j)) (hres j) (hres l)
        (hnodes j) (htree j) htr hjl
    · have hsame : tree j = tree l := by
        by_contra htr
        exact IsFamilyReserve.ne_of_ne_tree (hcoh (tree j) (htree j)) (hres j) (hres l)
          (hnodes j) (htree j) htr hjl
      have hl := hres l
      rw [← hsame] at hl
      exact (hres j).1.ne_of_incomparable hl.1 hinc hjl
  set P : Finset BitString := Finset.image R Finset.univ with hP
  have hcard : P.card = Fintype.card ι := by
    rw [hP, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hlen : ∀ p ∈ P, p.length = epsDepth := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.1
  have hnb : ∀ p ∈ P, ∃ s ∈ familyAllocated n T sm, p <+: s ∨ s <+: p := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, hRv⟩ := (hres j).1.2.1
    obtain ⟨y, hy, hyv⟩ :=
      allocationSubset_getAlloc_root (hcoh (tree j) (htree j)) (x j) (hnodes j) v hv
    refine ⟨y, ?_, List.prefix_or_prefix_of_prefix hRv hyv⟩
    refine Finset.mem_biUnion.mpr ⟨⟨tree j, htree j⟩, Finset.mem_univ _, ?_⟩
    exact List.mem_toFinset.mpr hy
  have havoid : ∀ p ∈ P, ∀ u ∈ A, ¬ (p <+: u ∨ u <+: p) := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hres j).1.2.2.2
  have hmass := familyGrayMass_ge_of_coarse_cells (n := n) (T := T) (A := A) (sm := sm)
    hed P hlen hnb havoid
  rwa [hcard] at hmass

/-- **From reserved intervals to the winning condition.** Once the reserved
mass held at one time `T` covers both the average-gray requirement and the
amplified total root request, the family gray goal is met. This is the shape in
which the half-step of SUV p. 143 cashes in its reserves. -/
theorem familyGrayGoal_of_familyReserves
    {kappa beta : ℚ} {epsDepth deltaDepth n T b : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {cm : ℕ → FamilyClientMove} {sm : ℕ → FamilyServerMove}
    (hcoh : ∀ i, i < n → serverMoveCoherent b (familyServerMoveAt (sm T) i))
    {ι : Type*} [Fintype ι]
    (tree : ι → ℕ) (x : ι → GacsDayNode) (R : ι → BitString)
    (htree : ∀ j, tree j < n)
    (hnodes : ∀ j, ∀ c ∈ x j, c < b)
    (hdistinct : ∀ j l, j ≠ l → tree j ≠ tree l ∨ ¬ (x j <+: x l ∨ x l <+: x j))
    (hres : ∀ j, IsFamilyReserve epsDepth A n (tree j) (sm T) (x j) (R j))
    (hbeta : (n : ℚ) * beta ≤ (Fintype.card ι : ℚ) * (1 / 2 : ℚ) ^ epsDepth)
    (hroot : kappa * totalRootRequest n (cm T)
      ≤ (Fintype.card ι : ℚ) * (1 / 2 : ℚ) ^ epsDepth)
    (hprogress : (n : ℚ) * beta ≤ kappa * totalRootRequest n (cm T)) :
    familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm := by
  have hmass := familyGrayMass_ge_of_familyReserves (deltaDepth := deltaDepth) hed hcoh
    tree x R htree hnodes hdistinct hres
  exact ⟨T, le_trans hbeta hmass, le_trans hroot hmass, hprogress⟩

/-- The same bound in the form the half-step uses it: `m` sons with reserved
intervals cap the reserved mass `m * epsilon` from below by the gray mass. -/
theorem familyGrayMass_ge_of_reserves_finset
    {epsDepth deltaDepth n T i b : ℕ} (hed : epsDepth ≤ deltaDepth)
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hcoh : serverMoveCoherent b (familyServerMoveAt (sm T) i)) (hi : i < n)
    (X : Finset GacsDayNode)
    (hnodes : ∀ y ∈ X, ∀ c ∈ y, c < b)
    (hincomp : ∀ y ∈ X, ∀ z ∈ X, y ≠ z → ¬ (y <+: z ∨ z <+: y))
    (hres : ∀ y ∈ X, hasReserve epsDepth A (familyServerMoveAt (sm T) i) y) :
    (X.card : ℚ) * (1 / 2 : ℚ) ^ epsDepth ≤
      familyGrayMass epsDepth deltaDepth n T A sm := by
  classical
  choose R hR using fun y : {y // y ∈ X} => hres y.1 y.2
  have hcard : Fintype.card {y // y ∈ X} = X.card := Fintype.card_coe X
  have hmain := familyGrayMass_ge_of_reserves (deltaDepth := deltaDepth) hed hcoh hi
    (ι := {y // y ∈ X}) (fun y => y.1) R
    (fun j => hnodes j.1 j.2)
    (fun j l hjl => hincomp j.1 j.2 l.1 l.2 (fun h => hjl (Subtype.ext h)))
    hR
  rwa [hcard] at hmain

end Kolmogorov
