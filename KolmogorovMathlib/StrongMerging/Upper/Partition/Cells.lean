import KolmogorovMathlib.StrongMerging.ExtraDefs
import KolmogorovMathlib.StrongMerging.Upper.Tradeoff

/-!
# The partition step: cells, the partition identity and computability

The stars, residual cells and partition cell of the partition step, their elementary
facts, the partition identity, the comparison with the selection of H05, the congruence
of cells computed from tables of complete runs, and the computability of the cell.

Part of `KolmogorovMathlib.StrongMerging.Upper.Partition`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Upper

namespace Partition

/-! ### Stars, residual cells and the partition cell -/

/-- The star of the typed endpoint `(side, w)` in the shape graph `P`: the shape edges whose
`side` output (`sideOut`: row output for `false`, column output for `true`) is `w`. -/
noncomputable def shapeStar (P : ShapeParams) (side : Bool) (w : BitString) : Finset BitString :=
  (shapeEdges P).filter fun y => sideOut P side y = w

/-- The residual cell of `z`: the residual `L_F` of the first listed block `F` whose residual
contains `z` (`firstResidualBlock`), with default `{z}`. -/
noncomputable def residualCell (P : ShapeParams) (R L J : ℕ) (z : BitString) : Finset BitString :=
  ((firstResidualBlock P R L J z).map fun p => residual P R L p.1 p.2).getD {z}

/-- The shape graph of the string `z` read from two output maps: data length `|z|` and the floor
buckets of the two outputs at `z`. -/
noncomputable def pointShape (fA fB : BitString → BitString) (z : BitString) : ShapeParams :=
  ⟨fA, fB, z.length, Nat.log 2 (parseModel (fA z)).card, Nat.log 2 (parseModel (fB z)).card⟩

/-- The cell of `z` inside its shape graph `P` (with `P.n = |z|`): in the small-degree branch
`min a b ≤ JL` the star of the larger bucket's endpoint (column star if `a ≤ b`, row star
otherwise), and otherwise the residual cell, with `L = c₂ H`, `J = ⌊n / R⌋ + 1`. -/
noncomputable def shapeCell (P : ShapeParams) (c₂ R e : ℕ) (z : BitString) : Finset BitString :=
  if min P.a P.b ≤ (P.n / R + 1) * (c₂ * baseBudget P.n e) then
    shapeStar P (decide (P.a ≤ P.b)) (sideOut P (decide (P.a ≤ P.b)) z)
  else residualCell P R (c₂ * baseBudget P.n e) (P.n / R + 1) z

/-- **The partition cell** (`cor:partition`, tex ~579): `{z}` if `|z| ≤ 1` or an output does not
contain `z`, and otherwise the cell of `z` in its shape graph (`shapeCell`). -/
noncomputable def partCell (fA fB : BitString → BitString) (c₂ R e : ℕ) (z : BitString) :
    Finset BitString :=
  if z.length ≤ 1 ∨ z ∉ parseModel (fA z) ∨ z ∉ parseModel (fB z) then {z}
  else shapeCell (pointShape fA fB z) c₂ R e z

/-- The partition cell read from the witnesses at the hardwired exponent `R`. -/
noncomputable def partModelAt (c₂ R : ℕ) (pA pB : BitString) (e : ℕ) (z : BitString) :
    Finset BitString :=
  partCell (progOut pA) (progOut pB) c₂ R e z

/-- The partition cell with a rule: `R = clipR n (ρ n e)` at `n = |z|`. -/
noncomputable def partModel (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ) (pA pB : BitString) (e : ℕ)
    (z : BitString) : Finset BitString :=
  partModelAt c₂ (clipR z.length (ρ z.length e)) pA pB e z

/-- The partition cell read from two output tables. -/
noncomputable def partCellT (c₂ R e : ℕ) (TA TB : List (BitString × BitString))
    (z : BitString) : Finset BitString :=
  partCell (tableOut TA) (tableOut TB) c₂ R e z

/-! ### Elementary facts -/

/-- The data length of an instance shape. -/
@[simp] theorem instShape_n (pA pB : BitString) (n a b : ℕ) : (instShape pA pB n a b).n = n :=
  rfl

/-- The row bucket of an instance shape. -/
@[simp] theorem instShape_a (pA pB : BitString) (n a b : ℕ) : (instShape pA pB n a b).a = a :=
  rfl

/-- The column bucket of an instance shape. -/
@[simp] theorem instShape_b (pA pB : BitString) (n a b : ℕ) : (instShape pA pB n a b).b = b :=
  rfl

/-- Membership in a star. -/
theorem mem_shapeStar {P : ShapeParams} {side : Bool} {w y : BitString} :
    y ∈ shapeStar P side w ↔ y ∈ shapeEdges P ∧ sideOut P side y = w := by
  rw [shapeStar, Finset.mem_filter]

/-- A star lies inside the model listed by its endpoint label: an edge `y` with `side` output `w`
lies in `parseModel (sideOut P side y) = parseModel w`. -/
theorem shapeStar_subset (P : ShapeParams) (side : Bool) (w : BitString) :
    shapeStar P side w ⊆ parseModel w := by
  intro y hy
  rw [mem_shapeStar, shapeEdges, Finset.mem_filter] at hy
  obtain ⟨⟨-, hE⟩, hw⟩ := hy
  unfold IsShapeEdge at hE
  rw [← hw]
  cases side
  · exact hE.1
  · exact hE.2.1

/-- Membership in the list of `(depth, block)` pairs. -/
theorem mem_blockPairs {P : ShapeParams} {R L J : ℕ} {p : ℕ × Finset BitString} :
    p ∈ blockPairs P R L J ↔ p.1 < J ∧ p.2 ∈ level P R L p.1 := by
  unfold blockPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, hp⟩
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hp
    exact ⟨List.mem_range.mp hj, hF⟩
  · rintro ⟨hj, hF⟩
    exact ⟨p.1, List.mem_range.mpr hj, List.mem_map.mpr ⟨p.2, hF, rfl⟩⟩

/-- A selected pair is listed and its residual contains the string. -/
theorem firstResidualBlock_some {P : ShapeParams} {R L J : ℕ} {z : BitString}
    {p : ℕ × Finset BitString} (h : firstResidualBlock P R L J z = some p) :
    p ∈ blockPairs P R L J ∧ z ∈ residual P R L p.1 p.2 := by
  unfold firstResidualBlock at h
  have h1 := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using h1⟩

/-- **Ancestors** (tex ~588, "the residuals over all levels are pairwise disjoint").  Every block
at depth `j + 1 + d` lies inside a child of some depth-`j` block.

Proof: induction on `d`.  For `d = 0` a depth-`(j+1)` block is a child of a depth-`j`
block (`level`, `List.mem_flatMap`).  For `d + 1` the block is a child of a depth-`(j+1+d)` block
`F''` (so a subset of it, `children_residual_spec`), and the induction hypothesis applies to
`F''`. -/
theorem exists_ancestor (P : ShapeParams) (R L j : ℕ) :
    ∀ d, ∀ F' ∈ level P R L (j + 1 + d), ∃ F ∈ level P R L j, ∃ T ∈ children P R L j F,
      F' ⊆ T
  | 0, F', hF' => by
    rw [Nat.add_zero, level, List.mem_flatMap] at hF'
    obtain ⟨F, hF, hT⟩ := hF'
    exact ⟨F, hF, F', hT, subset_rfl⟩
  | d + 1, F', hF' => by
    rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, level, List.mem_flatMap] at hF'
    obtain ⟨F'', hF'', hT⟩ := hF'
    obtain ⟨F, hF, T, hT', hsub⟩ := exists_ancestor P R L j d F'' hF''
    exact ⟨F, hF, T, hT', ((children_residual_spec P R L _ F'').1 F' hT).2.trans hsub⟩

/-- **A residual is disjoint from every deeper block.**

Proof: write the deeper depth as `j + 1 + d`; `exists_ancestor` gives a depth-`j` block
`G` and a child `T ⊇ F'`.  If `G = F`, the child `T` is disjoint from the residual of `F`
(`children_residual_spec`).  Otherwise `G` and `F` are distinct members of the pairwise disjoint
depth-`j` list (`level_pairwise_disjoint`, `List.Pairwise.forall`), the residual lies in `F` and
`T` lies in `G`. -/
theorem disjoint_residual_of_lt (P : ShapeParams) (R L : ℕ) {j j' : ℕ} (hjj : j < j')
    {F F' : Finset BitString} (hF : F ∈ level P R L j) (hF' : F' ∈ level P R L j') :
    Disjoint (residual P R L j F) F' := by
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + 1 + d := ⟨j' - j - 1, by omega⟩
  obtain ⟨G, hG, T, hT, hsub⟩ := exists_ancestor P R L j d F' hF'
  refine Finset.disjoint_of_subset_right hsub ?_
  by_cases hGF : G = F
  · subst hGF
    exact ((children_residual_spec P R L j G).2.2.1 T hT).symm
  · have hdis : Disjoint F G := (level_pairwise_disjoint P R L j).forall hF hG (Ne.symm hGF)
    exact Finset.disjoint_of_subset_left (children_residual_spec P R L j F).2.2.2.1
      (Finset.disjoint_of_subset_right ((children_residual_spec P R L j G).1 T hT).2 hdis)

/-- **Residuals of distinct listed blocks are disjoint** (tex ~588).

Proof: write `p = (j, F)`, `p' = (j', F')` with `mem_blockPairs`.  If `j = j'` then
`F ≠ F'` are members of the pairwise disjoint depth-`j` list (`level_pairwise_disjoint`,
`List.Pairwise.forall`) and residuals are subsets (`children_residual_spec`).  If `j < j'` or
`j' < j` use `disjoint_residual_of_lt` and `residual ⊆ block`. -/
theorem disjoint_residual_of_mem_blockPairs {P : ShapeParams} {R L J : ℕ}
    {p p' : ℕ × Finset BitString} (hp : p ∈ blockPairs P R L J) (hp' : p' ∈ blockPairs P R L J)
    (hne : p ≠ p') : Disjoint (residual P R L p.1 p.2) (residual P R L p'.1 p'.2) := by
  rw [mem_blockPairs] at hp hp'
  obtain ⟨j, F⟩ := p
  obtain ⟨j', F'⟩ := p'
  simp only at hp hp' ⊢
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact Finset.disjoint_of_subset_right (children_residual_spec P R L j' F').2.2.2.1
      (disjoint_residual_of_lt P R L hlt hp.2 hp'.2)
  · subst heq
    have hFF : F ≠ F' := fun h => hne (by rw [h])
    have hdis : Disjoint F F' := (level_pairwise_disjoint P R L j).forall hp.2 hp'.2 hFF
    exact Finset.disjoint_of_subset_left (children_residual_spec P R L j F).2.2.2.1
      (Finset.disjoint_of_subset_right (children_residual_spec P R L j F').2.2.2.1 hdis)
  · exact (Finset.disjoint_of_subset_right (children_residual_spec P R L j F).2.2.2.1
      (disjoint_residual_of_lt P R L hgt hp'.2 hp.2)).symm

/-- **The residual containing a string is unique**: if `y` lies in the residual of a listed pair
`p`, the selection at `y` is `p`. -/
theorem firstResidualBlock_eq_of_mem {P : ShapeParams} {R L J : ℕ} {y : BitString}
    {p : ℕ × Finset BitString} (hp : p ∈ blockPairs P R L J) (hy : y ∈ residual P R L p.1 p.2) :
    firstResidualBlock P R L J y = some p := by
  cases hfind : firstResidualBlock P R L J y with
  | none =>
    unfold firstResidualBlock at hfind
    have := List.find?_eq_none.mp hfind p hp
    simp [hy] at this
  | some p' =>
    obtain ⟨hp', hy'⟩ := firstResidualBlock_some hfind
    by_contra hne
    have hne' : p' ≠ p := fun h => hne (by rw [h])
    exact Finset.disjoint_left.mp (disjoint_residual_of_mem_blockPairs hp' hp hne') hy' hy

/-- The residual cell contains its string. -/
theorem mem_residualCell_self (P : ShapeParams) (R L J : ℕ) (z : BitString) :
    z ∈ residualCell P R L J z := by
  unfold residualCell
  cases h : firstResidualBlock P R L J z with
  | none => exact Finset.mem_singleton_self z
  | some p => exact (firstResidualBlock_some h).2

/-- A member of a residual cell is the string itself, or a shape edge with the same residual
cell. -/
theorem residualCell_eq_of_mem {P : ShapeParams} {R L J : ℕ} {z y : BitString}
    (hy : y ∈ residualCell P R L J z) :
    y = z ∨ (y ∈ shapeEdges P ∧ residualCell P R L J y = residualCell P R L J z) := by
  unfold residualCell at hy ⊢
  cases h : firstResidualBlock P R L J z with
  | none =>
    rw [h] at hy
    exact Or.inl (Finset.mem_singleton.mp hy)
  | some p =>
    rw [h] at hy
    obtain ⟨hp, -⟩ := firstResidualBlock_some h
    have hy' : y ∈ residual P R L p.1 p.2 := hy
    refine Or.inr ⟨?_, ?_⟩
    · exact level_subset P R L p.1 p.2 (mem_blockPairs.mp hp).2
        ((children_residual_spec P R L p.1 p.2).2.2.2.1 hy')
    · rw [firstResidualBlock_eq_of_mem hp hy']
      rfl

/-- The residual cell lies inside the parent selected by H05 (default `{z}`). -/
theorem residualCell_subset (P : ShapeParams) (R L J : ℕ) (z : BitString) :
    residualCell P R L J z ⊆ ((firstResidualBlock P R L J z).map Prod.snd).getD {z} := by
  unfold residualCell
  cases h : firstResidualBlock P R L J z with
  | none => exact subset_rfl
  | some p => exact (children_residual_spec P R L p.1 p.2).2.2.2.1

/-- A shape edge of the shape of `z` has the length of `z`, lies in both of its outputs, and has
the same shape. -/
theorem mem_shapeEdges_pointShape {fA fB : BitString → BitString} {z y : BitString}
    (hy : y ∈ shapeEdges (pointShape fA fB z)) :
    y.length = z.length ∧ y ∈ parseModel (fA y) ∧ y ∈ parseModel (fB y) ∧
      pointShape fA fB y = pointShape fA fB z := by
  rw [shapeEdges, Finset.mem_filter, mem_stringsOfLength] at hy
  obtain ⟨hlen, hE⟩ := hy
  unfold IsShapeEdge at hE
  obtain ⟨h1, h2, h3, h4⟩ := hE
  refine ⟨hlen, h1, h2, ?_⟩
  simp only [pointShape] at hlen h3 h4 ⊢
  rw [hlen, h3, h4]

/-- A string passing the guard is a shape edge of its own shape. -/
theorem mem_shapeEdges_pointShape_self {fA fB : BitString → BitString} {z : BitString}
    (hg : ¬ (z.length ≤ 1 ∨ z ∉ parseModel (fA z) ∨ z ∉ parseModel (fB z))) :
    z ∈ shapeEdges (pointShape fA fB z) := by
  simp only [not_or, not_le, not_not] at hg
  rw [shapeEdges, Finset.mem_filter, mem_stringsOfLength]
  refine ⟨rfl, ?_⟩
  unfold IsShapeEdge
  exact ⟨hg.2.1, hg.2.2, rfl, rfl⟩

/-! ### The partition identity -/

/-- The cell of a shape edge contains it. -/
theorem mem_shapeCell_self (P : ShapeParams) (c₂ R e : ℕ) {z : BitString}
    (hz : z ∈ shapeEdges P) : z ∈ shapeCell P c₂ R e z := by
  unfold shapeCell
  split_ifs
  · exact mem_shapeStar.mpr ⟨hz, rfl⟩
  · exact mem_residualCell_self P _ _ _ z

/-- **Every cell contains its input** (`cor:partition`). -/
theorem mem_partCell_self (fA fB : BitString → BitString) (c₂ R e : ℕ) (z : BitString) :
    z ∈ partCell fA fB c₂ R e z := by
  unfold partCell
  split_ifs with hg
  · exact Finset.mem_singleton_self z
  · exact mem_shapeCell_self _ c₂ R e (mem_shapeEdges_pointShape_self hg)

/-- A member of a shape cell is the string itself, or a shape edge with the same cell. -/
theorem shapeCell_eq_of_mem {P : ShapeParams} {c₂ R e : ℕ} {z y : BitString}
    (hy : y ∈ shapeCell P c₂ R e z) :
    y = z ∨ (y ∈ shapeEdges P ∧ shapeCell P c₂ R e y = shapeCell P c₂ R e z) := by
  unfold shapeCell at hy ⊢
  split_ifs at hy ⊢ with hs
  · obtain ⟨hyE, hside⟩ := mem_shapeStar.mp hy
    exact Or.inr ⟨hyE, by rw [hside]⟩
  · exact residualCell_eq_of_mem hy

/-- **Members of a cell return the same cell** (`cor:partition`, tex ~585–597): a member `y` of
the cell of `z` has the length of `z` and the same cell. -/
theorem partCell_eq_of_mem {fA fB : BitString → BitString} {c₂ R e : ℕ} {z y : BitString}
    (hy : y ∈ partCell fA fB c₂ R e z) :
    y.length = z.length ∧ partCell fA fB c₂ R e y = partCell fA fB c₂ R e z := by
  unfold partCell at hy
  split_ifs at hy with hg
  · rw [Finset.mem_singleton.mp hy]
    exact ⟨rfl, rfl⟩
  · rcases shapeCell_eq_of_mem hy with rfl | ⟨hyE, hc⟩
    · exact ⟨rfl, rfl⟩
    · obtain ⟨hlen, h1, h2, hsh⟩ := mem_shapeEdges_pointShape hyE
      have hgy : ¬ (y.length ≤ 1 ∨ y ∉ parseModel (fA y) ∨ y ∉ parseModel (fB y)) := by
        simp only [not_or, not_le, not_not] at hg ⊢
        exact ⟨by omega, h1, h2⟩
      refine ⟨hlen, ?_⟩
      unfold partCell
      rw [ite_eq_right hgy, ite_eq_right hg, hsh, hc]

/-- **The partition identity for a rule** (`cor:partition`): every cell contains its input and
`y ∈ Q z ↔ Q y = Q z`. -/
theorem partModel_partition (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ) (pA pB : BitString) (e : ℕ) :
    (∀ z, z ∈ partModel c₂ ρ pA pB e z) ∧
      ∀ z y, y ∈ partModel c₂ ρ pA pB e z ↔
        partModel c₂ ρ pA pB e y = partModel c₂ ρ pA pB e z := by
  refine ⟨fun z => mem_partCell_self _ _ _ _ _ z, fun z y => ⟨fun hy => ?_, fun h => ?_⟩⟩
  · unfold partModel partModelAt at hy ⊢
    obtain ⟨hlen, heq⟩ := partCell_eq_of_mem hy
    rw [hlen]
    exact heq
  · rw [← h]
    exact mem_partCell_self _ _ _ _ _ y

/-! ### Comparison with the selection of H05 -/

/-- **The new cell lies inside H05's selection** (tex ~598–606): a star lies inside the selected
original model, a residual inside its parent, and the defaults agree. -/
theorem partModelAt_subset_selectModelAt (c₂ R : ℕ) (pA pB : BitString) (e : ℕ)
    (z : BitString) : partModelAt c₂ R pA pB e z ⊆ selectModelAt c₂ R pA pB e z := by
  unfold partModelAt partCell selectModelAt
  by_cases hg : z.length ≤ 1 ∨ z ∉ parseModel (progOut pA z) ∨ z ∉ parseModel (progOut pB z)
  · rw [ite_eq_left hg, ite_eq_left hg]
  · rw [ite_eq_right hg, ite_eq_right hg]
    unfold shapeCell
    by_cases hs : min (Nat.log 2 (parseModel (progOut pA z)).card)
        (Nat.log 2 (parseModel (progOut pB z)).card) ≤
        (z.length / R + 1) * (c₂ * baseBudget z.length e)
    · rw [ite_eq_left hs, ite_eq_left (show min (pointShape (progOut pA) (progOut pB) z).a
        (pointShape (progOut pA) (progOut pB) z).b ≤
        ((pointShape (progOut pA) (progOut pB) z).n / R + 1) *
          (c₂ * baseBudget (pointShape (progOut pA) (progOut pB) z).n e) from hs)]
      by_cases hab : Nat.log 2 (parseModel (progOut pA z)).card ≤
          Nat.log 2 (parseModel (progOut pB z)).card
      · rw [ite_eq_left hab]
        have hd : decide ((pointShape (progOut pA) (progOut pB) z).a ≤
            (pointShape (progOut pA) (progOut pB) z).b) = true := decide_eq_true hab
        rw [hd]
        exact shapeStar_subset _ _ _
      · rw [ite_eq_right hab]
        have hd : decide ((pointShape (progOut pA) (progOut pB) z).a ≤
            (pointShape (progOut pA) (progOut pB) z).b) = false := decide_eq_false hab
        rw [hd]
        exact shapeStar_subset _ _ _
    · rw [ite_eq_right hs, ite_eq_right (show ¬ (min (pointShape (progOut pA) (progOut pB) z).a
        (pointShape (progOut pA) (progOut pB) z).b ≤
        ((pointShape (progOut pA) (progOut pB) z).n / R + 1) *
          (c₂ * baseBudget (pointShape (progOut pA) (progOut pB) z).n e)) from hs)]
      exact residualCell_subset _ _ _ _ _

/-- At an instance the shape of the actual string is the instance shape. -/
theorem pointShape_progOut {pA pB x : BitString} {A B : Finset BitString}
    (hA : progOut pA x = canonicalFiniteSetCode A) (hB : progOut pB x = canonicalFiniteSetCode B) :
    pointShape (progOut pA) (progOut pB) x =
      instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card) := by
  simp only [pointShape, instShape, hA, hB, parseModel_canonicalFiniteSetCode]

/-- At an instance (`|x| ≥ 2`, outputs `A, B ∋ x`) the cell is the shape cell of the instance
shape. -/
theorem partModelAt_eq_shapeCell {c₂ R e : ℕ} {pA pB x : BitString} {A B : Finset BitString}
    (hx : 2 ≤ x.length) (hA : progOut pA x = canonicalFiniteSetCode A)
    (hB : progOut pB x = canonicalFiniteSetCode B) (hxA : x ∈ A) (hxB : x ∈ B) :
    partModelAt c₂ R pA pB e x =
      shapeCell (instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card)) c₂ R e x := by
  have hne : ¬ (x.length ≤ 1 ∨ x ∉ parseModel (progOut pA x) ∨ x ∉ parseModel (progOut pB x)) := by
    rw [hA, hB, parseModel_canonicalFiniteSetCode, parseModel_canonicalFiniteSetCode]
    simp only [not_or, not_le, not_not]
    exact ⟨by omega, hxA, hxB⟩
  unfold partModelAt partCell
  rw [ite_eq_right hne, pointShape_progOut hA hB]

/-! ### Congruence: tables of complete runs give the same cell -/

/-- **Stars only read outputs at the data length.**

Proof: `shapeEdges_congr` rewrites the edge set; on an edge `y` (of length `n`) the two
`side` outputs agree (`ShapeParams.AgreeOn`), so the filters agree (`Finset.filter_congr`,
`cases side`, `sideOut`). -/
theorem shapeStar_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (side : Bool) (w : BitString) :
    shapeStar P side w = shapeStar Q side w := by
  have hE := shapeEdges_congr h
  obtain ⟨hn, -, -, hout⟩ := h
  unfold shapeStar
  rw [hE]
  apply Finset.filter_congr
  intro y hy
  rw [shapeEdges, Finset.mem_filter, mem_stringsOfLength] at hy
  obtain ⟨h1, h2⟩ := hout y (hy.1.trans hn.symm)
  cases side <;> simp [sideOut, h1, h2]

/-- **Residual cells only read outputs at the data length.**

Proof: `firstResidualBlock_congr` gives the same selected pair; its block is a set of
strings of length `n` (`firstResidualBlock_some`, `mem_blockPairs`, `length_eq_of_mem_level`), so
its residual agrees (`children_residual_congr`). -/
theorem residualCell_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (R L J : ℕ) (z : BitString) :
    residualCell P R L J z = residualCell Q R L J z := by
  unfold residualCell
  rw [← firstResidualBlock_congr h R L J z]
  cases hf : firstResidualBlock P R L J z with
  | none => rfl
  | some p =>
    obtain ⟨hp, -⟩ := firstResidualBlock_some hf
    exact congrArg (fun T => (some T : Option (Finset BitString)).getD {z})
      (children_residual_congr h R L p.1
        (length_eq_of_mem_level P R L p.1 (mem_blockPairs.mp hp).2)).2

/-- **Shape cells only read outputs at the data length** (for a string `z` of that length).

Proof: `P` and `Q` have the same `n, a, b`, so the branch test and the side agree; the
endpoint label `sideOut P side z = sideOut Q side z` since `|z| = n`; conclude with
`shapeStar_congr` and `residualCell_congr`. -/
theorem shapeCell_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (c₂ R e : ℕ) {z : BitString}
    (hz : z.length = P.n) : shapeCell P c₂ R e z = shapeCell Q c₂ R e z := by
  have hstar := shapeStar_congr h
  have hres := residualCell_congr h
  obtain ⟨hn, ha, hb, hout⟩ := h
  have hside : ∀ side, sideOut P side z = sideOut Q side z := by
    intro side
    cases side <;> simp [sideOut, (hout z hz).1, (hout z hz).2]
  unfold shapeCell
  rw [hn, ha, hb, hside, hstar, hres]

/-- **Cells only read outputs at the data length.**  If two pairs of output maps agree on all
strings of the length of `z`, the cells of `z` agree.

Proof: the guard reads only `fA z`, `fB z`; the two point shapes agree at the data length
(`ShapeParams.AgreeOn`: same `n`, buckets read at `z`, outputs agree on length-`|z|` strings);
conclude with `shapeCell_congr`. -/
theorem partCell_congr {fA fB gA gB : BitString → BitString} (c₂ R e : ℕ) {z : BitString}
    (h : ∀ y : BitString, y.length = z.length → fA y = gA y ∧ fB y = gB y) :
    partCell fA fB c₂ R e z = partCell gA gB c₂ R e z := by
  obtain ⟨hA, hB⟩ := h z rfl
  have hag : (pointShape fA fB z).AgreeOn (pointShape gA gB z) := by
    refine ⟨rfl, ?_, ?_, fun y hy => h y hy⟩
    · simp only [pointShape, hA]
    · simp only [pointShape, hB]
  unfold partCell
  rw [hA, hB, shapeCell_congr hag c₂ R e rfl]

/-- **Tables of complete runs give the semantic cell** on every input. -/
theorem partCellT_eq {pA pB z : BitString} {TA TB : List (BitString × BitString)}
    (hA : TA ∈ runTable pA z.length) (hB : TB ∈ runTable pB z.length) (c₂ R e : ℕ) :
    partCellT c₂ R e TA TB z = partModelAt c₂ R pA pB e z :=
  partCell_congr c₂ R e fun _ hy =>
    ⟨tableOut_of_mem_runTable hA hy, tableOut_of_mem_runTable hB hy⟩

/-! ### Computability -/

/-- **Stars are computable from the tables.**  The code of the star of `(side, w)` in the shape
read from two tables at `(n, a, b)` is primitive recursive.

Proof: the canonical point list of the shape-edge code (`shapeEdges_code_primrec` with
`fA = tableOut ∘ fst`, `fB = tableOut ∘ snd`) is filtered by the primitive recursive label test
`sideOut (tableShape …) side y = w` (`Primrec.cond` on the side, `Primrec.eq`), via
`primrec_list_filter` and `canonicalFiniteSetCode_toFinset_primrec`, as in the proof of
`localBlockCode_primrec`. -/
theorem shapeStarCode_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × Bool × BitString =>
      canonicalFiniteSetCode (shapeStar (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
        q.2.2.1 q.2.2.2) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hE : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × Bool × BitString => canonicalPointListOfCode (canonicalFiniteSetCode
        (shapeEdges (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2))) :=
    (canonicalPointListOfCode_primrec.comp ((shapeEdges_code_primrec _ _ hA hB).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))).of_eq fun q => rfl
  have hside : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × Bool × BitString) (z : BitString) =>
      sideOut (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.1 z := by
    refine (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (tableOut_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (tableOut_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).of_eq fun x => ?_
    rcases x with ⟨⟨T, nab, side, w⟩, z⟩
    cases side <;> rfl
  have htest : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × Bool × BitString) (z : BitString) =>
      decide (sideOut (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.1 z =
        q.2.2.2) :=
    Primrec.eq.decide.comp hside
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hfilt := primrec_list_filter hE htest
  refine (canonicalFiniteSetCode_toFinset_primrec.comp hfilt).of_eq fun q => ?_
  rw [canonicalPointListOfCode_canonicalFiniteSetCode]
  congr 1
  ext y
  simp only [List.mem_toFinset, List.mem_filter, mem_canonicalFinsetList, decide_eq_true_eq,
    shapeStar, Finset.mem_filter]

/-- The code of a residual cell through the coded selection: the form produced by
`firstResidualBlock_primrec` and `residual_code_primrec`. -/
theorem residualCell_code_eq (P : ShapeParams) (R L J : ℕ) (z : BitString) :
    canonicalFiniteSetCode (residualCell P R L J z) =
      (((firstResidualBlock P R L J z).map fun p => (p.1, canonicalFiniteSetCode p.2)).map
        fun p => canonicalFiniteSetCode (residual P R L p.1 (parseModel p.2))).getD
        (canonicalFiniteSetCode {z}) := by
  unfold residualCell
  cases firstResidualBlock P R L J z with
  | none => rfl
  | some p => simp [parseModel_canonicalFiniteSetCode]

/-- `sideOut` as a `cond` on the side. -/
theorem sideOut_eq_cond (P : ShapeParams) (side : Bool) (z : BitString) :
    sideOut P side z = cond side (P.outB z) (P.outA z) := by
  cases side <;> rfl

/-- **Residual cells are computable from the tables.**

Proof: as `selectResidualCode_primrec`: `firstResidualBlock_primrec` gives the selected
depth and block code; map it by `residual_code_primrec` (after
`parseModel_canonicalFiniteSetCode`) with `Primrec.option_map`, and default to the singleton code
(`singleton_code_primrec`, `Primrec.option_getD`). -/
theorem residualCellCode_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString =>
      canonicalFiniteSetCode (residualCell (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
        q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hin : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString => ((q.1, q.2.1, q.2.2.1), q.2.2.2) :=
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hF : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString =>
      (firstResidualBlock (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2) q.2.2.1.1
        q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2).map fun p => (p.1, canonicalFiniteSetCode p.2) :=
    ((firstResidualBlock_primrec _ _ hA hB).comp hin).of_eq fun q => rfl
  have hin2 : Primrec fun r : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString) × (ℕ × BitString) =>
      ((r.1.1, r.1.2.1, (r.1.2.2.1.1, r.1.2.2.1.2.1, r.2.1)), r.2.2) :=
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst)))).pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).pair
            (Primrec.fst.comp Primrec.snd))))).pair (Primrec.snd.comp Primrec.snd)
  have hmap : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString) (p : ℕ × BitString) =>
      canonicalFiniteSetCode (residual (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
        q.2.2.1.1 q.2.2.1.2.1 p.1 (parseModel p.2)) :=
    ((residual_code_primrec _ _ hA hB).comp hin2).of_eq fun r => rfl
  have hz : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × BitString => q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.option_getD.comp (Primrec.option_map hF hmap)
    (singleton_code_primrec.comp hz)
  exact h.of_eq fun q => (residualCell_code_eq _ _ _ _ _).symm

/-- **The table cell is primitive recursive** in `(c₂, R, e)`, the two tables and the input.

Proof: as `selectModelAtT_code_primrec`: the guard, the buckets, `L = c₂ H`,
`J = ⌊n / R⌋ + 1` and the branch test are primitive recursive; the point shape read from the
tables is `tableShape TA TB |z| a b` (definitionally); the two branches are
`shapeStarCode_primrec` (side `decide (a ≤ b)`, label `Primrec.cond` of the two table outputs)
and `residualCellCode_primrec`; combine with `Primrec.ite` and `of_eq` (`split_ifs`). -/
theorem partCellT_code_primrec :
    Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) × List (BitString × BitString)) ×
        BitString =>
      canonicalFiniteSetCode (partCellT q.1.1 q.1.2.1 q.1.2.2 q.2.1.1 q.2.1.2 q.2.2) := by
  have hz : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.2.2 := Primrec.snd.comp Primrec.snd
  have hT : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.2.1 := Primrec.fst.comp Primrec.snd
  have hoA := tableOut_primrec.comp (Primrec.fst.comp hT) hz
  have hoB := tableOut_primrec.comp (Primrec.snd.comp hT) hz
  have hn := Primrec.list_length.comp hz
  have ha := parseModel_logCard_primrec.comp hoA
  have hb := parseModel_logCard_primrec.comp hoB
  have hc : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.1 := Primrec.fst.comp Primrec.fst
  have hR : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have he : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hL := Primrec.nat_mul.comp hc (baseBudget_primrec.comp hn he)
  have hJ := Primrec.succ.comp (Primrec.nat_div.comp hn hR)
  have hmemA := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoA)
  have hmemB := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoB)
  have hguard := (Primrec.nat_le.comp hn (Primrec.const 1)).or (hmemA.not.or hmemB.not)
  have hsmall := Primrec.nat_le.comp (Primrec.nat_min.comp ha hb) (Primrec.nat_mul.comp hJ hL)
  have hside := Primrec.nat_le.decide.comp ha hb
  have hlab := Primrec.cond hside hoB hoA
  have hstar := shapeStarCode_primrec.comp
    (hT.pair ((hn.pair (ha.pair hb)).pair (hside.pair hlab)))
  have hres := residualCellCode_primrec.comp
    (hT.pair ((hn.pair (ha.pair hb)).pair ((hR.pair (hL.pair hJ)).pair hz)))
  refine (Primrec.ite hguard (singleton_code_primrec.comp hz)
    (Primrec.ite hsmall hstar hres)).of_eq fun q => ?_
  unfold partCellT partCell shapeCell
  by_cases hg : q.2.2.length ≤ 1 ∨ q.2.2 ∉ parseModel (tableOut q.2.1.1 q.2.2) ∨
      q.2.2 ∉ parseModel (tableOut q.2.1.2 q.2.2)
  · rw [ite_eq_left hg, ite_eq_left hg]
  · rw [ite_eq_right hg, ite_eq_right hg]
    by_cases hs : min (Nat.log 2 (parseModel (tableOut q.2.1.1 q.2.2)).card)
        (Nat.log 2 (parseModel (tableOut q.2.1.2 q.2.2)).card) ≤
        (q.2.2.length / q.1.2.1 + 1) * (q.1.1 * baseBudget q.2.2.length q.1.2.2)
    · rw [ite_eq_left hs, ite_eq_left (show
        min (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).a
          (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).b ≤
        ((pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).n / q.1.2.1 + 1) *
          (q.1.1 * baseBudget (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).n
            q.1.2.2) from hs), sideOut_eq_cond]
      rfl
    · rw [ite_eq_right hs, ite_eq_right (show ¬
        (min (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).a
          (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).b ≤
        ((pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).n / q.1.2.1 + 1) *
          (q.1.1 * baseBudget (pointShape (tableOut q.2.1.1) (tableOut q.2.1.2) q.2.2).n
            q.1.2.2)) from hs)]
      rfl

end Partition

end Kolmogorov.StrongMerging.Upper
