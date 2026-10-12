import KolmogorovMathlib.StrongMerging.Upper.Hierarchy.Extract

/-!
# The canonical hierarchy of small subgraphs (blueprint H01, H02)

`sublinear-merging.tex`, section "A canonical hierarchy of small subgraphs" (tex ~301) and the
residual stopping argument (tex ~382–550); appendix `bp-upper-hierarchy`.

* **H01 (`UpperExtract`).**  `extract elig F` repeatedly selects the first eligible subset of the
  current remainder (`firstEligible`: the first sublist of the canonical sorted list
  `canonicalFinsetList rem` whose set is eligible), records it as a child and removes it; the cap
  is part of `elig` and is fixed from the original parent.  `upperExtract`: the children are
  eligible, pairwise disjoint subsets of `F`, disjoint from the residual, children and residual
  cover `F`, and no subset of the residual is eligible.
* **H02 (`UpperHierarchy`).**  With shrink exponent `R` and step `L`, depth-`j` thresholds are
  `rowThr = 2^(a - jL)`, `colThr = 2^(b - jL)` and the cap of a block is `⌊|F| / 2^R⌋`
  (`blockCap`).  `level 0 = [G]` and `level (j+1)` lists the children of all depth-`j` blocks.
  `upperHierarchy`: blocks at one depth are pairwise disjoint subsets of `G`; positive-depth blocks
  are nonempty with the depth-`j` minimum degrees (nothing is claimed at depth zero); a depth-`j`
  block has `|F| 2^(jR) ≤ 2ⁿ` edges; and `level J = []` once `n < JR`.

Interface for H03–H05 (decoders, residual bound, selector):
* `card_rowIncidentBlocks_lt`, `card_colIncidentBlocks_lt`: fewer than `2^(jL+1)` depth-`j` blocks
  meet a fixed row/column (needs `jL ≤ a`, resp. `jL ≤ b`): one global local rank of `jL + 1` bits.
* `firstResidualBlock`: the selected depth and parent block of a string (the first block in the
  global depth-ordered list whose residual contains it); `firstResidualBlock_spec`.
* `coreFree_of_subset_residual`: a subset of a residual of size at most the cap is core-free for
  the next-depth capacities `shapeCap` — the hypothesis of `upperOnlineOrientation` in the residual
  compression argument (H04).

The first part of the development is in `KolmogorovMathlib.StrongMerging.Upper.Hierarchy.Extract`,
imported here.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### H02: the canonical hierarchy -/

/-- The depth-`j` row threshold `d_row(j) = 2^(a - jL)` (natural subtraction; it is the intended
value when `jL ≤ a`, which the hierarchy branch guarantees through `a > JL`). -/
def rowThr (P : ShapeParams) (L j : ℕ) : ℕ :=
  2 ^ (P.a - j * L)

/-- The depth-`j` column threshold `d_col(j) = 2^(b - jL)`. -/
def colThr (P : ShapeParams) (L j : ℕ) : ℕ :=
  2 ^ (P.b - j * L)

/-- The capacities of the shape vertices at depth `j`: rows get `rowThr`, columns `colThr`. -/
def shapeCap (P : ShapeParams) (L j : ℕ) : BitString ⊕ BitString → ℕ :=
  Sum.elim (fun _ => rowThr P L j) (fun _ => colThr P L j)

/-- The cap `M(F) = ⌊|F| / 2^R⌋` of a parent block, fixed from the original parent size. -/
def blockCap (R : ℕ) (F : Finset BitString) : ℕ :=
  F.card / 2 ^ R

/-- Eligibility of a child of a depth-`j` parent with cap `M`: nonempty, at most `M` edges, and
every incident row and column has degree at least the depth-`(j+1)` threshold. -/
def ChildElig (P : ShapeParams) (L j M : ℕ) (T : Finset BitString) : Prop :=
  T.Nonempty ∧ T.card ≤ M ∧
    ∀ z ∈ T, rowThr P L (j + 1) ≤ rowDeg P T (P.outA z) ∧ colThr P L (j + 1) ≤ colDeg P T (P.outB z)

instance (P : ShapeParams) (L j M : ℕ) : DecidablePred (ChildElig P L j M) := fun T => by
  unfold ChildElig
  infer_instance

/-- The children of a depth-`j` block `F`. -/
def children (P : ShapeParams) (R L j : ℕ) (F : Finset BitString) : List (Finset BitString) :=
  (extract (ChildElig P L j (blockCap R F)) F).1

/-- The residual `L_F` of a depth-`j` block `F`. -/
def residual (P : ShapeParams) (R L j : ℕ) (F : Finset BitString) : Finset BitString :=
  (extract (ChildElig P L j (blockCap R F)) F).2

/-- The depth-`j` list of blocks: `level 0 = [G]`, and `level (j+1)` lists the children of the
depth-`j` blocks in order. -/
noncomputable def level (P : ShapeParams) (R L : ℕ) : ℕ → List (Finset BitString)
  | 0 => [shapeEdges P]
  | j + 1 => (level P R L j).flatMap (children P R L j)

/-- `upperExtract` specialized to the children and residual of a block. -/
theorem children_residual_spec (P : ShapeParams) (R L j : ℕ) (F : Finset BitString) :
    (∀ T ∈ children P R L j F, ChildElig P L j (blockCap R F) T ∧ T ⊆ F) ∧
      (children P R L j F).Pairwise Disjoint ∧
      (∀ T ∈ children P R L j F, Disjoint T (residual P R L j F)) ∧
      residual P R L j F ⊆ F ∧
      (∀ z ∈ F, z ∈ residual P R L j F ∨ ∃ T ∈ children P R L j F, z ∈ T) ∧
      ∀ T ⊆ residual P R L j F, ¬ ChildElig P L j (blockCap R F) T :=
  upperExtract (fun _ h => h.1) F

/-- Every block of the hierarchy is a set of shape edges. -/
theorem level_subset (P : ShapeParams) (R L : ℕ) :
    ∀ j, ∀ F ∈ level P R L j, F ⊆ shapeEdges P
  | 0, F, hF => by
    rw [level, List.mem_singleton] at hF
    rw [hF]
  | j + 1, F, hF => by
    rw [level, List.mem_flatMap] at hF
    obtain ⟨F', hF', hF⟩ := hF
    exact ((children_residual_spec P R L j F').1 F hF).2.trans (level_subset P R L j F' hF')

/-- A child of a depth-`j` block is a nonempty block with the depth-`(j+1)` minimum degrees and
at most `⌊|parent| / 2^R⌋` edges. -/
theorem mem_level_succ (P : ShapeParams) (R L j : ℕ) {T : Finset BitString}
    (hT : T ∈ level P R L (j + 1)) :
    ∃ F ∈ level P R L j, T ⊆ F ∧ ChildElig P L j (blockCap R F) T := by
  rw [level, List.mem_flatMap] at hT
  obtain ⟨F, hF, hT⟩ := hT
  exact ⟨F, hF, ((children_residual_spec P R L j F).1 T hT).2,
    ((children_residual_spec P R L j F).1 T hT).1⟩

/-- Blocks at one depth are pairwise disjoint.

Proof sketch: induction on `j`.  Depth `0` is a singleton list.  For `j + 1` use
`List.pairwise_flatMap`: the children of one parent are pairwise disjoint
(`children_residual_spec`), and children of two parents at different positions of the
pairwise-disjoint depth-`j` list are disjoint because each child is a subset of its parent
(`Finset.disjoint_of_subset_left/right`). -/
theorem level_pairwise_disjoint (P : ShapeParams) (R L : ℕ) :
    ∀ j, (level P R L j).Pairwise Disjoint
  | 0 => by simp [level]
  | j + 1 => by
    rw [level, List.pairwise_flatMap]
    refine ⟨fun F _ => (children_residual_spec P R L j F).2.1, ?_⟩
    exact (level_pairwise_disjoint P R L j).imp fun {F₁ F₂} h T₁ hT₁ T₂ hT₂ =>
      Finset.disjoint_of_subset_left ((children_residual_spec P R L j F₁).1 T₁ hT₁).2
        (Finset.disjoint_of_subset_right ((children_residual_spec P R L j F₂).1 T₂ hT₂).2 h)

/-- **Size shrinkage.**  A depth-`j` block has at most `2^(n - jR)` edges, in the integer form
`|F| 2^(jR) ≤ 2ⁿ`. -/
theorem card_mul_pow_le_of_mem_level (P : ShapeParams) (R L : ℕ) :
    ∀ j, ∀ F ∈ level P R L j, F.card * 2 ^ (j * R) ≤ 2 ^ P.n
  | 0, F, hF => by
    rw [level, List.mem_singleton] at hF
    rw [hF, zero_mul, pow_zero, mul_one]
    exact card_shapeEdges_le P
  | j + 1, T, hT => by
    obtain ⟨F, hF, -, hel⟩ := mem_level_succ P R L j hT
    have h1 : T.card * 2 ^ R ≤ F.card :=
      (Nat.mul_le_mul_right _ hel.2.1).trans (Nat.div_mul_le_self _ _)
    calc T.card * 2 ^ ((j + 1) * R) = T.card * 2 ^ R * 2 ^ (j * R) := by
          rw [add_mul, one_mul, pow_add]
          ring
      _ ≤ F.card * 2 ^ (j * R) := Nat.mul_le_mul_right _ h1
      _ ≤ 2 ^ P.n := card_mul_pow_le_of_mem_level P R L j F hF

/-- **Positive-depth minimum degrees.**  A block at depth `j + 1` is nonempty and every incident
row and column has degree at least the depth-`(j+1)` threshold.  (No claim at depth zero.) -/
theorem minDeg_of_mem_level_succ (P : ShapeParams) (R L j : ℕ) {T : Finset BitString}
    (hT : T ∈ level P R L (j + 1)) :
    T.Nonempty ∧ ∀ z ∈ T, rowThr P L (j + 1) ≤ rowDeg P T (P.outA z) ∧
      colThr P L (j + 1) ≤ colDeg P T (P.outB z) := by
  obtain ⟨F, -, -, hel⟩ := mem_level_succ P R L j hT
  exact ⟨hel.1, hel.2.2⟩

/-- **Empty terminal level.**  If `n < JR` and `J ≥ 1` there are no depth-`J` blocks: a nonempty
block would have `2^(JR) ≤ |F| 2^(JR) ≤ 2ⁿ < 2^(JR)`. -/
theorem level_eq_nil (P : ShapeParams) (R L J : ℕ) (hJ : 0 < J) (hn : P.n < J * R) :
    level P R L J = [] := by
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  rw [List.eq_nil_iff_forall_not_mem]
  intro F hF
  obtain ⟨hne, -⟩ := minDeg_of_mem_level_succ P R L J' hF
  have hcard := card_mul_pow_le_of_mem_level P R L (J' + 1) F hF
  have hpos : 1 ≤ F.card := Finset.card_pos.mpr hne
  have hlt : 2 ^ P.n < 2 ^ ((J' + 1) * R) := Nat.pow_lt_pow_right (by norm_num) hn
  have : 2 ^ ((J' + 1) * R) ≤ F.card * 2 ^ ((J' + 1) * R) := Nat.le_mul_of_pos_left _ hpos
  omega

/-- **The canonical hierarchy (blueprint H02, `UpperHierarchy`).**  For every depth: the blocks
are pairwise disjoint sets of shape edges with `|F| 2^(jR) ≤ 2ⁿ`; blocks at positive depth are
nonempty with the depth minimum degrees (none is claimed at depth zero); every block is
partitioned by its children and its residual, which contains no eligible capped subset; and the
level `J` is empty once `J ≥ 1` and `n < JR` (as for `J = ⌊n / R⌋ + 1`, `R ≥ 1`). -/
theorem upperHierarchy (P : ShapeParams) (R L J : ℕ) (hJ : 0 < J) (hn : P.n < J * R) :
    (∀ j, (level P R L j).Pairwise Disjoint) ∧
      (∀ j, ∀ F ∈ level P R L j, F ⊆ shapeEdges P ∧ F.card * 2 ^ (j * R) ≤ 2 ^ P.n) ∧
      (∀ j, ∀ T ∈ level P R L (j + 1), T.Nonempty ∧ ∀ z ∈ T,
        rowThr P L (j + 1) ≤ rowDeg P T (P.outA z) ∧ colThr P L (j + 1) ≤ colDeg P T (P.outB z)) ∧
      (∀ j F, residual P R L j F ⊆ F ∧
        (∀ z ∈ F, z ∈ residual P R L j F ∨ ∃ T ∈ children P R L j F, z ∈ T) ∧
        ∀ T ⊆ residual P R L j F, ¬ ChildElig P L j (blockCap R F) T) ∧
      level P R L J = [] :=
  ⟨level_pairwise_disjoint P R L,
    fun j F hF => ⟨level_subset P R L j F hF, card_mul_pow_le_of_mem_level P R L j F hF⟩,
    fun j _ hT => minDeg_of_mem_level_succ P R L j hT,
    fun j F => ⟨(children_residual_spec P R L j F).2.2.2.1,
      (children_residual_spec P R L j F).2.2.2.2.1, (children_residual_spec P R L j F).2.2.2.2.2⟩,
    level_eq_nil P R L J hJ hn⟩

/-! ### Interface for the local decoders, the residual bound and the selector -/

/-- **Degrees add over disjoint blocks.**  For a list of pairwise disjoint subsets of `G`, the sum
of their row degrees at `w` is at most the row degree of `G` at `w`.

Proof sketch: induction on the list; the filter of the union of a disjoint family is the disjoint
union of the filters (`Finset.card_union_of_disjoint`), and the union is a subset of `G`
(`Finset.card_le_card`).  Equivalently pass to `(l.toFinset).biUnion` after noting that
duplicate nonempty sets are impossible in a pairwise disjoint list. -/
theorem sum_rowDeg_le (P : ShapeParams) (G : Finset BitString) (w : BitString) :
    ∀ l : List (Finset BitString), l.Pairwise Disjoint → (∀ F ∈ l, F ⊆ G) →
      (l.map fun F => rowDeg P F w).sum ≤ rowDeg P G w := by
  intro l
  induction l generalizing G with
  | nil => intro _ _; simp
  | cons F l ih =>
    intro hpw hsub
    rw [List.pairwise_cons] at hpw
    have hF : F ⊆ G := hsub F List.mem_cons_self
    have hrest : ∀ F' ∈ l, F' ⊆ G \ F := fun F' hF' z hz =>
      Finset.mem_sdiff.mpr ⟨hsub F' (List.mem_cons_of_mem _ hF') hz,
        fun hzF => Finset.disjoint_left.mp (hpw.1 F' hF') hzF hz⟩
    have h1 := ih (G \ F) hpw.2 hrest
    have h2 : rowDeg P F w + rowDeg P (G \ F) w = rowDeg P G w := by
      unfold rowDeg
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff),
        ← Finset.filter_union, Finset.union_sdiff_of_subset hF]
    rw [List.map_cons, List.sum_cons]
    omega

/-- **Degrees add over disjoint blocks (columns).**  As `sum_rowDeg_le` for column degrees. -/
theorem sum_colDeg_le (P : ShapeParams) (G : Finset BitString) (w : BitString) :
    ∀ l : List (Finset BitString), l.Pairwise Disjoint → (∀ F ∈ l, F ⊆ G) →
      (l.map fun F => colDeg P F w).sum ≤ colDeg P G w := by
  intro l
  induction l generalizing G with
  | nil => intro _ _; simp
  | cons F l ih =>
    intro hpw hsub
    rw [List.pairwise_cons] at hpw
    have hF : F ⊆ G := hsub F List.mem_cons_self
    have hrest : ∀ F' ∈ l, F' ⊆ G \ F := fun F' hF' z hz =>
      Finset.mem_sdiff.mpr ⟨hsub F' (List.mem_cons_of_mem _ hF') hz,
        fun hzF => Finset.disjoint_left.mp (hpw.1 F' hF') hzF hz⟩
    have h1 := ih (G \ F) hpw.2 hrest
    have h2 : colDeg P F w + colDeg P (G \ F) w = colDeg P G w := by
      unfold colDeg
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff),
        ← Finset.filter_union, Finset.union_sdiff_of_subset hF]
    rw [List.map_cons, List.sum_cons]
    omega

/-- **Counting arithmetic for the local rank.**  If `N · 2^(a - k) ≤ D < 2^(a+1)` and `k ≤ a`
then `N < 2^(k+1)`.

Proof sketch: `2^(a+1) = 2^(k+1) · 2^(a-k)` (`pow_add`, `k + 1 + (a - k) = a + 1`); if
`N ≥ 2^(k+1)` then `N 2^(a-k) ≥ 2^(a+1) > D`. -/
theorem lt_pow_of_mul_pow_le {N D a k : ℕ} (hk : k ≤ a) (hN : N * 2 ^ (a - k) ≤ D)
    (hD : D < 2 ^ (a + 1)) : N < 2 ^ (k + 1) := by
  by_contra hc
  replace hc := not_lt.mp hc
  have h1 : 2 ^ (a + 1) = 2 ^ (k + 1) * 2 ^ (a - k) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : 2 ^ (k + 1) * 2 ^ (a - k) ≤ N * 2 ^ (a - k) := Nat.mul_le_mul_right _ hc
  rw [← h1] at h2
  exact absurd hD (not_lt.mpr (h2.trans hN))

/-- **Few blocks at a row (tex ~330).**  If `jL ≤ a`, fewer than `2^(jL+1)` depth-`j` blocks
meet a fixed row label `w`: each meeting block has degree at least `2^(a - jL)` at `w` (positive
depth) or is the single depth-zero block, the blocks are disjoint, and `deg_G(w) < 2^(a+1)`. -/
theorem card_rowIncidentBlocks_lt (P : ShapeParams) (R L j : ℕ) (hj : j * L ≤ P.a)
    (w : BitString) :
    ((level P R L j).filter fun F => decide (∃ z ∈ F, P.outA z = w)).length < 2 ^ (j * L + 1) := by
  cases j with
  | zero =>
    calc ((level P R L 0).filter fun F => decide (∃ z ∈ F, P.outA z = w)).length
        ≤ (level P R L 0).length := List.length_filter_le _ _
      _ = 1 := by rw [level, List.length_singleton]
      _ < 2 ^ (0 * L + 1) := by simp
  | succ j =>
    set l := (level P R L (j + 1)).filter fun F => decide (∃ z ∈ F, P.outA z = w) with hl
    have hsub : l.Sublist (level P R L (j + 1)) := List.filter_sublist
    have hdisj : l.Pairwise Disjoint := (level_pairwise_disjoint P R L (j + 1)).sublist hsub
    have hG : ∀ F ∈ l, F ⊆ shapeEdges P := fun F hF => level_subset P R L (j + 1) F (hsub.subset hF)
    have hthr : ∀ F ∈ l, rowThr P L (j + 1) ≤ rowDeg P F w := by
      intro F hF
      have hF' := List.mem_filter.mp hF
      obtain ⟨z, hz, hzw⟩ := of_decide_eq_true hF'.2
      have := ((minDeg_of_mem_level_succ P R L j hF'.1).2 z hz).1
      rwa [hzw] at this
    have hsum : l.length * rowThr P L (j + 1) ≤ (l.map fun F => rowDeg P F w).sum := by
      have := List.length_nsmul_le_sum (l.map fun F => rowDeg P F w) (rowThr P L (j + 1))
        (fun x hx => by
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
          exact hthr F hF)
      simpa using this
    exact lt_pow_of_mul_pow_le hj
      (hsum.trans (sum_rowDeg_le P (shapeEdges P) w l hdisj hG)) (rowDeg_shapeEdges_lt P w)

/-- **Few blocks at a column (tex ~330).**  As `card_rowIncidentBlocks_lt`, for column labels
and `jL ≤ b`.

Proof sketch: repeat the proof of `card_rowIncidentBlocks_lt` with `colThr`, `colDeg`,
`sum_colDeg_le` and `colDeg_shapeEdges_lt`. -/
theorem card_colIncidentBlocks_lt (P : ShapeParams) (R L j : ℕ) (hj : j * L ≤ P.b)
    (w : BitString) :
    ((level P R L j).filter fun F => decide (∃ z ∈ F, P.outB z = w)).length < 2 ^ (j * L + 1) := by
  cases j with
  | zero =>
    calc ((level P R L 0).filter fun F => decide (∃ z ∈ F, P.outB z = w)).length
        ≤ (level P R L 0).length := List.length_filter_le _ _
      _ = 1 := by rw [level, List.length_singleton]
      _ < 2 ^ (0 * L + 1) := by simp
  | succ j =>
    set l := (level P R L (j + 1)).filter fun F => decide (∃ z ∈ F, P.outB z = w) with hl
    have hsub : l.Sublist (level P R L (j + 1)) := List.filter_sublist
    have hdisj : l.Pairwise Disjoint := (level_pairwise_disjoint P R L (j + 1)).sublist hsub
    have hG : ∀ F ∈ l, F ⊆ shapeEdges P := fun F hF => level_subset P R L (j + 1) F (hsub.subset hF)
    have hthr : ∀ F ∈ l, colThr P L (j + 1) ≤ colDeg P F w := by
      intro F hF
      have hF' := List.mem_filter.mp hF
      obtain ⟨z, hz, hzw⟩ := of_decide_eq_true hF'.2
      have := ((minDeg_of_mem_level_succ P R L j hF'.1).2 z hz).2
      rwa [hzw] at this
    have hsum : l.length * colThr P L (j + 1) ≤ (l.map fun F => colDeg P F w).sum := by
      have := List.length_nsmul_le_sum (l.map fun F => colDeg P F w) (colThr P L (j + 1))
        (fun x hx => by
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hx
          exact hthr F hF)
      simpa using this
    exact lt_pow_of_mul_pow_le hj
      (hsum.trans (sum_colDeg_le P (shapeEdges P) w l hdisj hG)) (colDeg_shapeEdges_lt P w)

/-- **Every edge stops at a residual before depth `J`.**  If `n < JR`, every shape edge `x` lies
in the residual of some block `F ∋ x` at some depth `j < J`.

Proof sketch: show by induction on `j ≤ J` that either `x` lies in a residual at some depth
`< j`, or `x` lies in some depth-`j` block: at depth `0`, `x ∈ G`; a block containing `x` either
has `x` in its residual or in a child (`children_residual_spec`), which is a depth-`(j+1)` block
(`List.mem_flatMap`).  At `j = J` the second case is impossible by `level_eq_nil` (`J ≥ 1`
follows from `n < JR`). -/
theorem exists_mem_residual (P : ShapeParams) (R L J : ℕ) (hn : P.n < J * R) {x : BitString}
    (hx : x ∈ shapeEdges P) :
    ∃ j < J, ∃ F ∈ level P R L j, x ∈ F ∧ x ∈ residual P R L j F := by
  have hJ : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · rw [h, zero_mul] at hn
      omega
    · exact h
  have key : ∀ j, (∃ j' < j, ∃ F ∈ level P R L j', x ∈ F ∧ x ∈ residual P R L j' F) ∨
      ∃ F ∈ level P R L j, x ∈ F := by
    intro j
    induction j with
    | zero => exact Or.inr ⟨shapeEdges P, by simp [level], hx⟩
    | succ j ih =>
      rcases ih with ⟨j', hj', F, hF, hxF, hxr⟩ | ⟨F, hF, hxF⟩
      · exact Or.inl ⟨j', by omega, F, hF, hxF, hxr⟩
      · rcases (children_residual_spec P R L j F).2.2.2.2.1 x hxF with hxr | ⟨T, hT, hxT⟩
        · exact Or.inl ⟨j, by omega, F, hF, hxF, hxr⟩
        · refine Or.inr ⟨T, ?_, hxT⟩
          rw [level, List.mem_flatMap]
          exact ⟨F, hF, hT⟩
  rcases key J with h | ⟨F, hF, -⟩
  · exact h
  · rw [level_eq_nil P R L J hJ hn] at hF
    simp at hF

/-- The global list of `(depth, block)` pairs for depths `0, …, J - 1`, in depth order. -/
noncomputable def blockPairs (P : ShapeParams) (R L J : ℕ) : List (ℕ × Finset BitString) :=
  (List.range J).flatMap fun j => (level P R L j).map fun F => (j, F)

/-- The depth and the parent block selected for a string `z`: the first pair in `blockPairs` whose
residual contains `z` (the parent of the first residual along `z`'s path). -/
noncomputable def firstResidualBlock (P : ShapeParams) (R L J : ℕ) (z : BitString) :
    Option (ℕ × Finset BitString) :=
  (blockPairs P R L J).find? fun p => decide (z ∈ residual P R L p.1 p.2)

/-- **Selection spec.**  For a shape edge `x` and `n < JR`, the selection returns a depth `j < J`
and a depth-`j` block `F ∋ x` with `x` in the residual of `F`.

Proof sketch: `exists_mem_residual` gives a pair in `blockPairs` (`List.mem_flatMap`,
`List.mem_range`, `List.mem_map`) satisfying the test, so `find?` is `some p`
(`List.find?_eq_none` excludes `none`); `List.find?_some` and `List.mem_of_find?_eq_some` give the
properties of `p`, and `residual ⊆ F` gives `x ∈ F`. -/
theorem firstResidualBlock_spec (P : ShapeParams) (R L J : ℕ) (hn : P.n < J * R)
    {x : BitString} (hx : x ∈ shapeEdges P) :
    ∃ j F, firstResidualBlock P R L J x = some (j, F) ∧ j < J ∧ F ∈ level P R L j ∧ x ∈ F ∧
      x ∈ residual P R L j F := by
  obtain ⟨j, hj, F, hF, -, hxr⟩ := exists_mem_residual P R L J hn hx
  have hmem : (j, F) ∈ blockPairs P R L J :=
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨F, hF, rfl⟩⟩
  cases hfind : firstResidualBlock P R L J x with
  | none =>
    unfold firstResidualBlock at hfind
    have := List.find?_eq_none.mp hfind (j, F) hmem
    simp [hxr] at this
  | some p =>
    unfold firstResidualBlock at hfind
    have h1 := List.find?_some hfind
    have h2 := List.mem_of_find?_eq_some hfind
    simp only [decide_eq_true_eq] at h1
    obtain ⟨j'', hj'', hpF⟩ := List.mem_flatMap.mp h2
    obtain ⟨F'', hF'', rfl⟩ := List.mem_map.mp hpF
    exact ⟨j'', F'', rfl, List.mem_range.mp hj'', hF'',
      (children_residual_spec P R L j'' F'').2.2.2.1 h1, h1⟩

/-- **Residual subsets are core-free (input to H04).**  A subset `E` of the residual of a
depth-`j` block `F` with at most `⌊|F| / 2^R⌋` edges has no core for the depth-`(j+1)` capacities:
such a core would be an eligible capped subset left in the residual. -/
theorem coreFree_of_subset_residual (P : ShapeParams) (R L j : ℕ) {F E : Finset BitString}
    (hE : E ⊆ residual P R L j F) (hcard : E.card ≤ blockCap R F) :
    CoreFree (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) E := by
  intro T hT hcore
  apply (children_residual_spec P R L j F).2.2.2.2.2 T (hT.trans hE)
  refine ⟨hcore.1, (Finset.card_le_card hT).trans hcard, fun z hz => ⟨?_, ?_⟩⟩
  · have hv : Sum.inl (P.outA z) ∈ incidentVerts (shapeSrc P) (shapeTgt P) T :=
      mem_incidentVerts.mpr ⟨z, hz, Or.inl rfl⟩
    have := hcore.2 _ hv
    rw [degIn_shape_inl] at this
    exact this
  · have hv : Sum.inr (P.outB z) ∈ incidentVerts (shapeSrc P) (shapeTgt P) T :=
      mem_incidentVerts.mpr ⟨z, hz, Or.inr rfl⟩
    have := hcore.2 _ hv
    rw [degIn_shape_inr] at this
    exact this

/-- Capacities are at most `2^(max a b)`, as needed for the bound `W ≤ 2^(n + 1 + max a b)` of
`sum_incidentVerts_le_pow`. -/
theorem shapeCap_le (P : ShapeParams) (L j : ℕ) (v : BitString ⊕ BitString) :
    shapeCap P L j v ≤ 2 ^ max P.a P.b := by
  cases v
  · simp only [shapeCap, Sum.elim_inl, rowThr]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (le_max_left _ _))
  · simp only [shapeCap, Sum.elim_inr, colThr]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (le_max_right _ _))

/-- The next-depth capacities are positive. -/
theorem shapeCap_pos (P : ShapeParams) (L j : ℕ) (v : BitString ⊕ BitString) :
    0 < shapeCap P L j v := by
  cases v <;> simp only [shapeCap, Sum.elim_inl, Sum.elim_inr, rowThr, colThr] <;> positivity

/-! ### Congruence: the hierarchy only reads outputs at the data length -/

/-- `List.find?` only reads its test on the members of the list. -/
theorem find?_congr_of_mem {β : Type*} {p q : β → Bool} :
    ∀ {l : List β}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    cases hq : q x
    · simp only [List.find?_cons, h x List.mem_cons_self, hq]
      exact find?_congr_of_mem fun y hy => h y (List.mem_cons_of_mem _ hy)
    · simp only [List.find?_cons, h x List.mem_cons_self, hq]

/-- `List.flatMap` only reads its function on the members of the list. -/
theorem flatMap_congr_of_mem {β γ : Type*} {f g : β → List γ} :
    ∀ {l : List β}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr_of_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Blocks of the hierarchy consist of strings of the data length. -/
theorem length_eq_of_mem_level (P : ShapeParams) (R L j : ℕ) {F : Finset BitString}
    (hF : F ∈ level P R L j) : ∀ z ∈ F, z.length = P.n := fun _ hz =>
  (mem_stringsOfLength _ _).mp (Finset.mem_filter.mp (level_subset P R L j F hF hz)).1

/-- **Extraction only reads eligibility on subsets of the parent.**

Proof sketch: generalize to `extractAux` with any remainder `rem ⊆ F` and induct on the fuel:
`firstEligible` tests only `s.toFinset` for sublists `s` of `canonicalFinsetList rem`, which are
subsets of `rem ⊆ F` (so the two `List.find?` calls agree), and the next remainder `rem \ T` is
again a subset of `F`. -/
theorem extract_congr {elig elig' : Finset BitString → Prop} [DecidablePred elig]
    [DecidablePred elig'] {F : Finset BitString} (h : ∀ T ⊆ F, (elig T ↔ elig' T)) :
    extract elig F = extract elig' F := by
  have hfirst : ∀ rem ⊆ F, firstEligible elig rem = firstEligible elig' rem := by
    intro rem hrem
    unfold firstEligible
    rw [find?_congr_of_mem (q := fun s => decide (elig' s.toFinset))]
    intro s hs
    refine decide_eq_decide.mpr (h _ fun z hz => hrem ?_)
    rw [List.mem_toFinset] at hz
    exact mem_canonicalFinsetList.mp ((List.mem_sublists.mp hs).subset hz)
  have key : ∀ fuel, ∀ rem ⊆ F, extractAux elig fuel rem = extractAux elig' fuel rem := by
    intro fuel
    induction fuel with
    | zero => intro rem _; rfl
    | succ fuel ih =>
      intro rem hrem
      simp only [extractAux]
      rw [hfirst rem hrem]
      split
      · rfl
      · rename_i T _
        rw [ih (rem \ T) (Finset.sdiff_subset.trans hrem)]
  exact key _ F subset_rfl

/-- **Congruence of children and residuals.**  For parameter sets that agree at the data length
and a block of strings of that length, the children and the residual agree.

Proof sketch: by `extract_congr`, since for `T ⊆ F` the thresholds agree (same `a, b`) and
`rowDeg P T (P.outA z) = rowDeg Q T (Q.outA z)` for `z ∈ T` (all outputs read are on strings of
length `n`); similarly for columns. -/
theorem children_residual_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (R L j : ℕ)
    {F : Finset BitString} (hF : ∀ z ∈ F, z.length = P.n) :
    children P R L j F = children Q R L j F ∧ residual P R L j F = residual Q R L j F := by
  obtain ⟨hn, ha, hb, hout⟩ := h
  have hel : ∀ T ⊆ F, (ChildElig P L j (blockCap R F) T ↔ ChildElig Q L j (blockCap R F) T) := by
    intro T hT
    have hrow : ∀ z ∈ T, rowDeg P T (P.outA z) = rowDeg Q T (Q.outA z) := by
      intro z hz
      unfold rowDeg
      rw [← (hout z (hF z (hT hz))).1]
      congr 1
      exact Finset.filter_congr fun y hy => by rw [(hout y (hF y (hT hy))).1]
    have hcol : ∀ z ∈ T, colDeg P T (P.outB z) = colDeg Q T (Q.outB z) := by
      intro z hz
      unfold colDeg
      rw [← (hout z (hF z (hT hz))).2]
      congr 1
      exact Finset.filter_congr fun y hy => by rw [(hout y (hF y (hT hy))).2]
    unfold ChildElig rowThr colThr
    rw [ha, hb]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun z hz => ⟨by rw [← hrow z hz]; exact (h3 z hz).1,
        by rw [← hcol z hz]; exact (h3 z hz).2⟩⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun z hz => ⟨by rw [hrow z hz]; exact (h3 z hz).1,
        by rw [hcol z hz]; exact (h3 z hz).2⟩⟩
  have := extract_congr hel
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **Congruence of the hierarchy.**  Parameter sets that agree at the data length have the same
depth lists.

Proof sketch: induction on `j`; depth `0` is `shapeEdges_congr`; for `j + 1` use
`List.flatMap_congr` with `children_residual_congr`, since every block is a set of shape edges
(`level_subset`), hence of strings of length `n`. -/
theorem level_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (R L : ℕ) :
    ∀ j, level P R L j = level Q R L j
  | 0 => by simp only [level, shapeEdges_congr h]
  | j + 1 => by
    simp only [level]
    rw [← level_congr h R L j]
    exact flatMap_congr_of_mem fun F hF =>
      (children_residual_congr h R L j (length_eq_of_mem_level P R L j hF)).1

/-- **Congruence of the selection.**  Parameter sets that agree at the data length select the same
depth and block for every string.

Proof sketch: `blockPairs` agree by `level_congr`, and on each listed pair the residual test agrees
by `children_residual_congr` (blocks are sets of shape edges). -/
theorem firstResidualBlock_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (R L J : ℕ)
    (z : BitString) : firstResidualBlock P R L J z = firstResidualBlock Q R L J z := by
  unfold firstResidualBlock
  have hpairs : blockPairs P R L J = blockPairs Q R L J := by
    unfold blockPairs
    simp only [level_congr h R L]
  rw [← hpairs]
  apply find?_congr_of_mem
  intro p hp
  obtain ⟨j, -, hpF⟩ := List.mem_flatMap.mp hp
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hpF
  simp only [(children_residual_congr h R L j (length_eq_of_mem_level P R L j hF)).2]

/-! ### Computability of the finite hierarchy -/

/-- The canonical point list of a code is duplicate-free. -/
theorem childPR_nodup (w : BitString) : (canonicalPointListOfCode w).Nodup := by
  unfold canonicalPointListOfCode
  exact canonicalFinsetList_nodup _

/-- The row degree in a parsed model counts the canonical point list. -/
theorem childPR_rowDeg_parseModel (P : ShapeParams) (w v : BitString) :
    rowDeg P (parseModel w) v =
      (canonicalPointListOfCode w).countP fun y => decide (P.outA y = v) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((childPR_nodup w).filter _),
    rowDeg, parseModel, List.toFinset_filter]
  simp only [decide_eq_true_eq]

/-- The column degree in a parsed model counts the canonical point list. -/
theorem childPR_colDeg_parseModel (P : ShapeParams) (w v : BitString) :
    colDeg P (parseModel w) v =
      (canonicalPointListOfCode w).countP fun y => decide (P.outB y = v) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((childPR_nodup w).filter _),
    colDeg, parseModel, List.toFinset_filter]
  simp only [decide_eq_true_eq]

/-- The capped child-eligibility test in Boolean form on the canonical point list `lT` of the
candidate: nonempty, at most `M` entries, and every entry has row and column counts at least the
depth-`(j+1)` thresholds `2^(a - (j+1)L)`, `2^(b - (j+1)L)`. -/
def childEligBool (gA gB : BitString → BitString) (a b L j M : ℕ) (lT : List BitString) : Bool :=
  decide (0 < lT.length) && decide (lT.length ≤ M) &&
    lT.all fun z => decide (2 ^ (a - (j + 1) * L) ≤ lT.countP fun y => decide (gA y = gA z)) &&
      decide (2 ^ (b - (j + 1) * L) ≤ lT.countP fun y => decide (gB y = gB z))

/-- The child-eligibility test of a parsed candidate agrees with its Boolean form. -/
theorem decide_childElig_eq (P : ShapeParams) (L j M : ℕ) (w : BitString) :
    decide (ChildElig P L j M (parseModel w)) =
      childEligBool P.outA P.outB P.a P.b L j M (canonicalPointListOfCode w) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [ChildElig, childEligBool, ← Finset.card_pos, shapePR_card_parseModel,
    shapePR_mem_parseModel, childPR_rowDeg_parseModel, childPR_colDeg_parseModel, rowThr, colThr,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

/-- **The capped child-eligibility test is primitive recursive on codes.**  For witness output
maps depending primitive recursively on a parameter, deciding `ChildElig` of the set coded by `w`,
for the cap of the parent coded by `p.2` and the parameters `(n, a, b)`, `(R, L, j)`, is primitive
recursive.

Proof: `decide_childElig_eq` turns the test into `childEligBool` on the canonical point list of
the candidate code; the cap is `Primrec.nat_div` of the parent's list length by a power of two
(`shapePR_pow_primrec`); the degree condition is `list_all_primrec` of comparisons with
`list_countP_primrec` counts of equal outputs. -/
theorem childEligTest_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec₂ fun (p : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) (w : BitString) =>
      decide (ChildElig ⟨fA p.1.1, fB p.1.1, p.1.2.1.1, p.1.2.1.2.1, p.1.2.1.2.2⟩ p.1.2.2.2.1
        p.1.2.2.2.2 (blockCap p.1.2.2.1 (parseModel p.2)) (parseModel w)) := by
  -- the input `x = ((parameters, parent code), candidate code)`
  have hlT : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      canonicalPointListOfCode x.2 :=
    canonicalPointListOfCode_primrec.comp Primrec.snd
  have hM : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      (canonicalPointListOfCode x.1.2).length / 2 ^ x.1.1.2.2.1 :=
    Primrec.nat_div.comp
      (Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp
        (Primrec.snd.comp Primrec.fst)))
      (shapePR_pow_primrec.comp (Primrec.const 2)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
  have hne : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      decide (0 < (canonicalPointListOfCode x.2).length) :=
    Primrec.nat_lt.decide.comp (Primrec.const 0) (Primrec.list_length.comp hlT)
  have hcap : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      decide ((canonicalPointListOfCode x.2).length ≤
        (canonicalPointListOfCode x.1.2).length / 2 ^ x.1.1.2.2.1) :=
    Primrec.nat_le.decide.comp (Primrec.list_length.comp hlT) hM
  -- counts of equal row / column outputs inside the candidate, for an entry `z`
  have hcntA : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
      BitString => (canonicalPointListOfCode y.1.2).countP
        fun u => decide (fA y.1.1.1.1 u = fA y.1.1.1.1 y.2) := by
    have hp : Primrec₂ fun (y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString) (u : BitString) => decide (fA y.1.1.1.1 u = fA y.1.1.1.1 y.2) :=
      (Primrec.eq.decide.comp
        (hA.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))) Primrec.snd)
        (hA.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))) (Primrec.snd.comp Primrec.fst))).to₂
    exact list_countP_primrec (hlT.comp Primrec.fst) hp
  have hcntB : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
      BitString => (canonicalPointListOfCode y.1.2).countP
        fun u => decide (fB y.1.1.1.1 u = fB y.1.1.1.1 y.2) := by
    have hp : Primrec₂ fun (y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString) (u : BitString) => decide (fB y.1.1.1.1 u = fB y.1.1.1.1 y.2) :=
      (Primrec.eq.decide.comp
        (hB.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))) Primrec.snd)
        (hB.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst)))) (Primrec.snd.comp Primrec.fst))).to₂
    exact list_countP_primrec (hlT.comp Primrec.fst) hp
  -- the thresholds `2^(a - (j+1)L)`, `2^(b - (j+1)L)`
  have hthrA : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
      BitString => 2 ^ (y.1.1.1.2.1.2.1 - (y.1.1.1.2.2.2.2 + 1) * y.1.1.1.2.2.2.1) := by
    have hP : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst))
    have ha : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.1.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hP))
    have hL : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hP))
    have hj : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hP))
    exact shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp ha (Primrec.nat_mul.comp (Primrec.succ.comp hj) hL))
  have hthrB : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
      BitString => 2 ^ (y.1.1.1.2.1.2.2 - (y.1.1.1.2.2.2.2 + 1) * y.1.1.1.2.2.2.1) := by
    have hP : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          Primrec.fst))
    have hb : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.1.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hP))
    have hL : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hP))
    have hj : Primrec fun y : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString) ×
        BitString => y.1.1.1.2.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hP))
    exact shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp hb (Primrec.nat_mul.comp (Primrec.succ.comp hj) hL))
  have hall : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      (canonicalPointListOfCode x.2).all fun z =>
        decide (2 ^ (x.1.1.2.1.2.1 - (x.1.1.2.2.2.2 + 1) * x.1.1.2.2.2.1) ≤
          (canonicalPointListOfCode x.2).countP fun u => decide (fA x.1.1.1 u = fA x.1.1.1 z)) &&
        decide (2 ^ (x.1.1.2.1.2.2 - (x.1.1.2.2.2.2 + 1) * x.1.1.2.2.2.1) ≤
          (canonicalPointListOfCode x.2).countP fun u => decide (fB x.1.1.1 u = fB x.1.1.1 z)) := by
    have hp : Primrec₂ fun (x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString)
        (z : BitString) =>
        decide (2 ^ (x.1.1.2.1.2.1 - (x.1.1.2.2.2.2 + 1) * x.1.1.2.2.2.1) ≤
          (canonicalPointListOfCode x.2).countP fun u => decide (fA x.1.1.1 u = fA x.1.1.1 z)) &&
        decide (2 ^ (x.1.1.2.1.2.2 - (x.1.1.2.2.2.2 + 1) * x.1.1.2.2.2.1) ≤
          (canonicalPointListOfCode x.2).countP fun u => decide (fB x.1.1.1 u = fB x.1.1.1 z)) :=
      (Primrec.and.comp (Primrec.nat_le.decide.comp hthrA hcntA)
        (Primrec.nat_le.decide.comp hthrB hcntB)).to₂
    exact list_all_primrec hlT hp
  have h : Primrec fun x : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × BitString =>
      childEligBool (fA x.1.1.1) (fB x.1.1.1) x.1.1.2.1.2.1 x.1.1.2.1.2.2 x.1.1.2.2.2.1
        x.1.1.2.2.2.2 ((canonicalPointListOfCode x.1.2).length / 2 ^ x.1.1.2.2.1)
        (canonicalPointListOfCode x.2) :=
    Primrec.and.comp (Primrec.and.comp hne hcap) hall
  have h2 : Primrec₂ fun (p : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) (w : BitString) =>
      childEligBool (fA p.1.1) (fB p.1.1) p.1.2.1.2.1 p.1.2.1.2.2 p.1.2.2.2.1
        p.1.2.2.2.2 ((canonicalPointListOfCode p.2).length / 2 ^ p.1.2.2.1)
        (canonicalPointListOfCode w) := h.to₂
  refine h2.of_eq fun p w => ?_
  rw [decide_childElig_eq, blockCap, shapePR_card_parseModel]

/-- **Residuals are computable (blueprint H04, computability).**  The canonical code of the
residual of a coded block is primitive recursive in the parameters and the block code (the residual
decoder of H04 reconstructs `L_F` from `F`).

Proof: `extract_code_primrec` with `eligP` the capped child eligibility of the parent code
(`childEligTest_primrec`), composed with `q ↦ (q, q.2)`. -/
theorem residual_code_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      canonicalFiniteSetCode (residual ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩
        q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 (parseModel q.2)) := by
  have hE := extract_code_primrec (β := (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString)
    (fun p S => ChildElig ⟨fA p.1.1, fB p.1.1, p.1.2.1.1, p.1.2.1.2.1, p.1.2.1.2.2⟩ p.1.2.2.2.1
      p.1.2.2.2.2 (blockCap p.1.2.2.1 (parseModel p.2)) S)
    (childEligTest_primrec fA fB hA hB)
  exact (Primrec.snd.comp (hE.comp (Primrec.pair Primrec.id Primrec.snd))).of_eq fun q => rfl

/-- Replacing the depth (the last component) of a parameter tuple `(p, (n, a, b), (R, L, j))` by
`k` is primitive recursive. -/
theorem levelPR_setDepth_primrec {β : Type} [Primcodable β] :
    Primrec₂ fun (q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) (k : ℕ) =>
      ((q.1, q.2.1, (q.2.2.1, q.2.2.2.1, k)) : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := by
  have h : Primrec fun r : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × ℕ =>
      ((r.1.1, r.1.2.1, (r.1.2.2.1, r.1.2.2.2.1, r.2)) : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
            Primrec.snd)))
  exact h

/-- **Children codes are primitive recursive.**  The canonical codes of the children of a coded
block are primitive recursive in the parameters and the block code.

Proof: `extract_code_primrec` with the capped child eligibility of the parent code
(`childEligTest_primrec`), composed with `q ↦ (q, q.2)`; first component (as
`residual_code_primrec`, which takes the second component). -/
theorem levelPR_children_codes_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      (children ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩
        q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 (parseModel q.2)).map canonicalFiniteSetCode := by
  have hE := extract_code_primrec (β := (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString)
    (fun p S => ChildElig ⟨fA p.1.1, fB p.1.1, p.1.2.1.1, p.1.2.1.2.1, p.1.2.1.2.2⟩ p.1.2.2.2.1
      p.1.2.2.2.2 (blockCap p.1.2.2.1 (parseModel p.2)) S)
    (childEligTest_primrec fA fB hA hB)
  exact (Primrec.fst.comp (hE.comp (Primrec.pair Primrec.id Primrec.snd))).of_eq fun q => rfl

/-- **The level recursion on codes.**  Starting from the code of the shape edge set and replacing
every code by the codes of the children of the block it codes (at the current depth) computes the
codes of the depth-`j` blocks.

Proof: induction on `j`; the step is `List.flatMap_map`, `List.map_flatMap` and
`parseModel_canonicalFiniteSetCode` under the binder. -/
theorem levelPR_rec_eq (P : ShapeParams) (R L : ℕ) :
    ∀ j : ℕ, (Nat.rec (motive := fun _ => List BitString) [canonicalFiniteSetCode (shapeEdges P)]
      (fun k IH => IH.flatMap fun c =>
        (children P R L k (parseModel c)).map canonicalFiniteSetCode) j : List BitString) =
      (level P R L j).map canonicalFiniteSetCode
  | 0 => by
    rw [Nat.rec_zero, level, List.map_cons, List.map_nil]
  | j + 1 => by
    rw [Nat.rec_add_one, levelPR_rec_eq P R L j, level, List.flatMap_map, List.map_flatMap]
    simp only [parseModel_canonicalFiniteSetCode]

/-- **The step of the level recursion is primitive recursive.**  Replacing every code in a list
by the codes of the children (at depth `s.1`) of the block it codes is primitive recursive in the
parameters and `s = (k, codes)`.

Proof: `levelPR_children_codes_primrec` composed with the argument tuple, then
`Primrec.list_flatMap`. -/
theorem levelPR_step_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec₂ fun (q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) (s : ℕ × List BitString) =>
      s.2.flatMap fun c => (children ⟨fA q.1, fB q.1, q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩ q.2.2.1
        q.2.2.2.1 s.1 (parseModel c)).map canonicalFiniteSetCode := by
  have htup : Primrec fun r : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × (ℕ × List BitString)) ×
      BitString => (((r.1.1.1, r.1.1.2.1, (r.1.1.2.2.1, r.1.1.2.2.2.1, r.1.2.1)), r.2) :
        (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) :=
    Primrec.pair (levelPR_setDepth_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  have hg := (levelPR_children_codes_primrec fA fB hA hB).comp htup
  have hf : Primrec fun a : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × (ℕ × List BitString) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have h := Primrec.list_flatMap hf hg.to₂
  exact h

/-- **The base of the level recursion is primitive recursive**: the one-element list of the code
of the shape edge set (`shapeEdges_code_primrec`). -/
theorem levelPR_base_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      [canonicalFiniteSetCode (shapeEdges ⟨fA q.1, fB q.1, q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩)] := by
  have htup : Primrec fun q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      ((q.1, q.2.1) : β × ℕ × ℕ × ℕ) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have h1 := (shapeEdges_code_primrec fA fB hA hB).comp htup
  have h2 := Primrec.list_cons.comp h1 (Primrec.const ([] : List BitString))
  exact h2

/-- **The depth lists are computable (blueprint H02/H03, computability).**  For witness output
maps depending primitive recursively on a parameter `p : β` (in the application: a finite output
table read by `tableOut`), the canonical codes of the depth-`j` blocks are primitive recursive
(hence computable) in `p` and `(n, a, b)`, `(R, L, j)`.  This is the finite total computation of
the local block decoder (H03).

Proof: `Primrec.nat_rec'` on `j` with base `[code G]` (`levelPR_base_primrec`, from
`shapeEdges_code_primrec`) and step `codes ↦ codes.flatMap (children codes of the parsed parent at
depth k)` (`levelPR_step_primrec`, from `extract_code_primrec` and `childEligTest_primrec`); the
pointwise equation is `levelPR_rec_eq` (`List.flatMap_map`, `List.map_flatMap`,
`parseModel_canonicalFiniteSetCode`).  Implementation note: compose with the argument tuple
without an expected type (`have h := hc.comp htup`) — elaborating such a `.comp` against a stated
type made `isDefEq` unfold `children`/`extractAux` and time out. -/
theorem level_codes_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      (level ⟨fA q.1, fB q.1, q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩ q.2.2.1 q.2.2.2.1
        q.2.2.2.2).map canonicalFiniteSetCode := by
  have hj : Primrec fun q : β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrec := Primrec.nat_rec' hj (levelPR_base_primrec fA fB hA hB)
    (levelPR_step_primrec fA fB hA hB)
  refine hrec.of_eq fun q => ?_
  exact levelPR_rec_eq ⟨fA q.1, fB q.1, q.2.1.1, q.2.1.2.1, q.2.1.2.2⟩ q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- Membership in the decoded point list of a canonical code is membership in the set. -/
theorem levelPR_mem_code_iff (S : Finset BitString) (z : BitString) :
    z ∈ canonicalPointListOfCode (canonicalFiniteSetCode S) ↔ z ∈ S := by
  rw [canonicalPointListOfCode_canonicalFiniteSetCode, mem_canonicalFinsetList]

/-- The coded `(depth, block)` pairs: mapping the codes of the depth-`j` blocks to `(j, code)` and
concatenating over `j < J` codes `blockPairs`. -/
theorem levelPR_codedPairs_eq (P : ShapeParams) (R L J : ℕ) :
    ((List.range J).flatMap fun j => ((level P R L j).map canonicalFiniteSetCode).map
      fun c => (j, c)) =
      (blockPairs P R L J).map fun p => (p.1, canonicalFiniteSetCode p.2) := by
  rw [blockPairs, List.map_flatMap]
  simp only [List.map_map, Function.comp_def]

/-- **The selection on codes.**  Searching the coded `(depth, block)` pairs with the residual
membership test decided on codes gives the coded selection.

Proof: `levelPR_codedPairs_eq`, `List.find?_map`, then the tests agree pointwise by
`parseModel_canonicalFiniteSetCode` and `levelPR_mem_code_iff`. -/
theorem levelPR_find_eq (P : ShapeParams) (R L J : ℕ) (z : BitString) :
    (((List.range J).flatMap fun j => ((level P R L j).map canonicalFiniteSetCode).map
      fun c => (j, c)).find? fun p => decide (z ∈ canonicalPointListOfCode
        (canonicalFiniteSetCode (residual P R L p.1 (parseModel p.2))))) =
      (firstResidualBlock P R L J z).map fun p => (p.1, canonicalFiniteSetCode p.2) := by
  rw [levelPR_codedPairs_eq, List.find?_map, firstResidualBlock]
  apply congrArg
  apply find?_congr_of_mem
  intro p _
  refine decide_eq_decide.mpr ?_
  simp only [parseModel_canonicalFiniteSetCode, levelPR_mem_code_iff]

/-- **Coded pairs at one depth are primitive recursive**: the list of `(j, code F)` for the
depth-`j` blocks `F`, from `level_codes_primrec` and `Primrec.list_map`. -/
theorem levelPR_pairsAt_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec₂ fun (q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) (j : ℕ) =>
      ((level ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩ q.1.2.2.1 q.1.2.2.2.1
        j).map canonicalFiniteSetCode).map fun c => (j, c) := by
  have htup : Primrec fun r : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × ℕ =>
      ((r.1.1.1, r.1.1.2.1, (r.1.1.2.2.1, r.1.1.2.2.2.1, r.2)) :
        β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
    levelPR_setDepth_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hlev := (level_codes_primrec fA fB hA hB).comp htup
  have hpair : Primrec fun r : (((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × ℕ) ×
      BitString => (r.1.2, r.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h := Primrec.list_map hlev hpair.to₂
  exact h

/-- **The coded `(depth, block)` pairs are primitive recursive**: `List.flatMap` over
`List.range J` of `levelPR_pairsAt_primrec`. -/
theorem levelPR_codedPairs_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      (List.range q.1.2.2.2.2).flatMap fun j =>
        ((level ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩ q.1.2.2.1 q.1.2.2.2.1
          j).map canonicalFiniteSetCode).map fun c => (j, c) := by
  have hJ : Primrec fun q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      List.range q.1.2.2.2.2 :=
    Primrec.list_range.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have h := Primrec.list_flatMap hJ (levelPR_pairsAt_primrec fA fB hA hB)
  exact h

/-- **The residual test on codes is primitive recursive**: membership of the string `q.2` in the
decoded residual of the block coded by `p.2` at depth `p.1` (`residual_code_primrec`,
`canonicalPointListOfCode_primrec`, `bitString_mem_primrec`). -/
theorem levelPR_resTest_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec₂ fun (q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) (p : ℕ × BitString) =>
      decide (q.2 ∈ canonicalPointListOfCode (canonicalFiniteSetCode
        (residual ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩ q.1.2.2.1
          q.1.2.2.2.1 p.1 (parseModel p.2)))) := by
  have htup : Primrec fun r : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × (ℕ × BitString) =>
      (((r.1.1.1, r.1.1.2.1, (r.1.1.2.2.1, r.1.1.2.2.2.1, r.2.1)), r.2.2) :
        (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) :=
    Primrec.pair (levelPR_setDepth_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  have hres := (residual_code_primrec fA fB hA hB).comp htup
  have hz : Primrec fun r : ((β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString) × (ℕ × BitString) =>
      r.1.2 :=
    Primrec.snd.comp Primrec.fst
  have h := bitString_mem_primrec.comp hz (canonicalPointListOfCode_primrec.comp hres)
  exact h

/-- **The selection is computable (blueprint H05, computability).**  The selected depth and the
code of the selected block of a string are primitive recursive in the parameters `(n, a, b)`,
`(R, L, J)` and the string: the finite core of the total point selector.

Proof: `list_find?_primrec` over the coded `(depth, block)` pairs (`levelPR_codedPairs_primrec`,
a `List.flatMap` over `List.range J` of `level_codes_primrec`) with the residual membership test on
codes (`levelPR_resTest_primrec`, from `residual_code_primrec`); the pointwise equation is
`levelPR_find_eq` (`List.find?_map`, `parseModel_canonicalFiniteSetCode`). -/
theorem firstResidualBlock_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : (β × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      (firstResidualBlock ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩
        q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2).map fun p => (p.1, canonicalFiniteSetCode p.2) := by
  have hfind := list_find?_primrec (levelPR_codedPairs_primrec fA fB hA hB)
    (levelPR_resTest_primrec fA fB hA hB)
  refine hfind.of_eq fun q => ?_
  exact levelPR_find_eq ⟨fA q.1.1, fB q.1.1, q.1.2.1.1, q.1.2.1.2.1, q.1.2.1.2.2⟩ q.1.2.2.1
    q.1.2.2.2.1 q.1.2.2.2.2 q.2

end Kolmogorov.StrongMerging.Upper
