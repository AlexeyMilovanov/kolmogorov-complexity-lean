import KolmogorovMathlib.StoppingComplexity.Words

/-!
# Dyadic cells

Finite dyadic geometry of the stopping-allocation game (blueprint part 02, DEF-02 and
LEM-CELL-01; part 01 F1, last paragraph). A cell `(d, i)` denotes the half-open interval
`[i / 2^d, (i + 1) / 2^d)` with rational endpoints; disjointness, containment and containment
in `[0, U)` are decidable rational comparisons with integer-refinement characterizations
(DEF-02). Dyadic laminarity (LEM-CELL-01) is stated with the explicit depth-`a` ancestor
`cellAncestor`. The exact finite correspondence between cells inside `[0, 2^cap)` and binary
words of length `depth + cap` (`cellAddress`, `cellOfAddress`) turns disjointness into
incomparability and containment into the prefix relation (F1-CELL), so that no pointwise
binary expansion of a real number is ever used.
-/

namespace Kolmogorov

/-! ### Cells and their rational geometry -/

/-- A dyadic cell `(depth, index)`, denoting `[index / 2^depth, (index + 1) / 2^depth)`.
Blueprint 02 DEF-02. -/
abbrev DyadicCell := ℕ × ℕ

/-- Left endpoint `i / 2^d` of the cell `(d, i)`. Blueprint 02 DEF-02. -/
def cellLeft (c : DyadicCell) : ℚ := (c.2 : ℚ) / 2 ^ c.1

/-- Right endpoint `(i + 1) / 2^d` of the cell `(d, i)` (excluded). Blueprint 02 DEF-02. -/
def cellRight (c : DyadicCell) : ℚ := ((c.2 : ℚ) + 1) / 2 ^ c.1

/-- Length `2^{-d}` of a cell of depth `d`. Blueprint 02 DEF-02. -/
def cellLength (c : DyadicCell) : ℚ := (1 / 2 : ℚ) ^ c.1

/-- Two half-open cells are disjoint when one ends before (or where) the other begins;
touching cells are disjoint. Blueprint 02 DEF-02. -/
def CellsDisjoint (c c' : DyadicCell) : Prop :=
  cellRight c ≤ cellLeft c' ∨ cellRight c' ≤ cellLeft c

/-- `CellSubset c c'`: the cell `c` lies inside the cell `c'`. Blueprint 02 DEF-02. -/
def CellSubset (c c' : DyadicCell) : Prop :=
  cellLeft c' ≤ cellLeft c ∧ cellRight c ≤ cellRight c'

/-- Containment of a cell in `[0, U)`: `(i + 1) / 2^d ≤ U`. Blueprint 02 DEF-02. -/
def CellInCapacity (U : ℚ) (c : DyadicCell) : Prop := cellRight c ≤ U

/-- Disjointness of cells is decidable (rational comparisons). Blueprint 02 DEF-02. -/
instance instDecidableCellsDisjoint (c c' : DyadicCell) : Decidable (CellsDisjoint c c') := by
  unfold CellsDisjoint; infer_instance

/-- Containment of cells is decidable. Blueprint 02 DEF-02. -/
instance instDecidableCellSubset (c c' : DyadicCell) : Decidable (CellSubset c c') := by
  unfold CellSubset; infer_instance

/-- Containment in `[0, U)` is decidable. Blueprint 02 DEF-02. -/
instance instDecidableCellInCapacity (U : ℚ) (c : DyadicCell) :
    Decidable (CellInCapacity U c) := by
  unfold CellInCapacity; infer_instance

/-- The length of a cell is the difference of its endpoints. Blueprint 02 DEF-02. -/
theorem cellLength_eq_cellRight_sub_cellLeft (c : DyadicCell) :
    cellLength c = cellRight c - cellLeft c := by
  unfold cellLength cellRight cellLeft
  rw [← sub_div, add_sub_cancel_left, one_div_pow]

/-- All left endpoints are nonnegative. Blueprint 02 DEF-02. -/
theorem cellLeft_nonneg (c : DyadicCell) : 0 ≤ cellLeft c := by
  unfold cellLeft
  positivity

/-- The right endpoint `(i + 1) / 2^d` with its numerator read as a natural number. -/
private theorem cellRight_eq_natCast (c : DyadicCell) :
    cellRight c = ((c.2 + 1 : ℕ) : ℚ) / 2 ^ c.1 := by
  simp [cellRight]

/-- Comparison of the dyadic rationals `a / 2^d ≤ b / 2^e` by integer refinement to the common
depth `max d e`. -/
private theorem div_two_pow_le_div_two_pow_iff (a b d e : ℕ) :
    (a : ℚ) / 2 ^ d ≤ (b : ℚ) / 2 ^ e ↔ a * 2 ^ (max d e - d) ≤ b * 2 ^ (max d e - e) := by
  have key : ∀ x k : ℕ, k ≤ max d e →
      (x : ℚ) / 2 ^ k = ((x * 2 ^ (max d e - k) : ℕ) : ℚ) / 2 ^ max d e := by
    intro x k hk
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ (2 : ℚ) two_ne_zero hk]
    field_simp
  rw [key a d (le_max_left d e), key b e (le_max_right d e),
    div_le_div_iff_of_pos_right (by positivity), Nat.cast_le]

/-- Disjointness by integer refinement to the common depth `T = max d e`: compare the integer
intervals `[i · 2^(T-d), (i+1) · 2^(T-d))`. Blueprint 02 DEF-02. -/
theorem cellsDisjoint_iff_refined (c c' : DyadicCell) :
    CellsDisjoint c c' ↔
      (c.2 + 1) * 2 ^ (max c.1 c'.1 - c.1) ≤ c'.2 * 2 ^ (max c.1 c'.1 - c'.1) ∨
      (c'.2 + 1) * 2 ^ (max c.1 c'.1 - c'.1) ≤ c.2 * 2 ^ (max c.1 c'.1 - c.1) := by
  unfold CellsDisjoint cellLeft
  rw [cellRight_eq_natCast, cellRight_eq_natCast, div_two_pow_le_div_two_pow_iff,
    div_two_pow_le_div_two_pow_iff, max_comm c'.1 c.1]

/-- Containment by integer refinement to the common depth `T = max d e`.
Blueprint 02 DEF-02. -/
theorem cellSubset_iff_refined (c c' : DyadicCell) :
    CellSubset c c' ↔
      c'.2 * 2 ^ (max c.1 c'.1 - c'.1) ≤ c.2 * 2 ^ (max c.1 c'.1 - c.1) ∧
      (c.2 + 1) * 2 ^ (max c.1 c'.1 - c.1) ≤ (c'.2 + 1) * 2 ^ (max c.1 c'.1 - c'.1) := by
  unfold CellSubset cellLeft
  rw [cellRight_eq_natCast, cellRight_eq_natCast, div_two_pow_le_div_two_pow_iff,
    div_two_pow_le_div_two_pow_iff, max_comm c'.1 c.1]

/-- At a common depth, disjointness is inequality of the indices. Blueprint 02 DEF-02. -/
theorem cellsDisjoint_same_depth_iff {d i i' : ℕ} :
    CellsDisjoint (d, i) (d, i') ↔ i ≠ i' := by
  rw [cellsDisjoint_iff_refined]
  simp only [max_self, Nat.sub_self, pow_zero, mul_one]
  omega

/-! ### Dyadic laminarity -/

/-- If a depth-`a` cell meets a depth-`b` cell and `a ≤ b`, the depth-`a` cell contains the
depth-`b` cell. Blueprint 02 LEM-CELL-01. -/
theorem cellSubset_of_not_disjoint_of_depth_le {c c' : DyadicCell}
    (h : ¬ CellsDisjoint c c') (hd : c.1 ≤ c'.1) : CellSubset c' c := by
  rw [cellsDisjoint_iff_refined, max_eq_right hd] at h
  rw [cellSubset_iff_refined, max_eq_left hd]
  simp only [Nat.sub_self, pow_zero, mul_one] at h ⊢
  omega

/-- Dyadic laminarity: two aligned cells are disjoint or one contains the other.
Blueprint 02 LEM-CELL-01. -/
theorem cellsDisjoint_or_cellSubset (c c' : DyadicCell) :
    CellsDisjoint c c' ∨ CellSubset c c' ∨ CellSubset c' c := by
  by_cases h : CellsDisjoint c c'
  · exact Or.inl h
  rcases le_total c.1 c'.1 with hd | hd
  · exact Or.inr (Or.inr (cellSubset_of_not_disjoint_of_depth_le h hd))
  · have h' : ¬ CellsDisjoint c' c := fun h' => h (Or.symm h')
    exact Or.inr (Or.inl (cellSubset_of_not_disjoint_of_depth_le h' hd))

/-- The depth-`a` ancestor of a cell: Euclidean division of the index by `2^(d - a)`.
Blueprint 02 LEM-CELL-01. -/
def cellAncestor (c : DyadicCell) (a : ℕ) : DyadicCell := (a, c.2 / 2 ^ (c.1 - a))

/-- A cell lies inside its depth-`a` ancestor when `a ≤ d`. Blueprint 02 LEM-CELL-01. -/
theorem cellSubset_cellAncestor (c : DyadicCell) {a : ℕ} (ha : a ≤ c.1) :
    CellSubset c (cellAncestor c a) := by
  rw [cellSubset_iff_refined]
  simp only [cellAncestor, max_eq_left ha, Nat.sub_self, pow_zero, mul_one]
  have hpos : 0 < 2 ^ (c.1 - a) := by positivity
  exact ⟨Nat.div_mul_le_self _ _, by rw [add_one_mul]; exact Nat.lt_div_mul_add hpos⟩

/-- A cell inside another cell is at least as deep. -/
private theorem depth_le_of_cellSubset {c r : DyadicCell} (h : CellSubset c r) : r.1 ≤ c.1 := by
  by_contra hlt
  push_neg at hlt
  rw [cellSubset_iff_refined, max_eq_right hlt.le] at h
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  have h2 : 2 ≤ 2 ^ (r.1 - c.1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r.1 - c.1) := Nat.pow_le_pow_right two_pos (by omega)
  rw [add_one_mul] at h
  omega

/-- The ancestor at a given depth is unique: a cell containing `c` is the ancestor of `c` at
its own depth. Blueprint 02 LEM-CELL-01. -/
theorem cellAncestor_unique {c r : DyadicCell} (hr : CellSubset c r) :
    r = cellAncestor c r.1 := by
  have hd := depth_le_of_cellSubset hr
  rw [cellSubset_iff_refined, max_eq_left hd] at hr
  simp only [Nat.sub_self, pow_zero, mul_one] at hr
  refine Prod.ext rfl ?_
  simp only [cellAncestor]
  exact (Nat.div_eq_of_lt_le hr.1 hr.2).symm

/-- A cell inside a cell contained in `[0, U)` is itself contained in `[0, U)`.
Blueprint 02 DEF-02. -/
theorem cellInCapacity_of_cellSubset {U : ℚ} {c c' : DyadicCell} (h : CellSubset c c')
    (hc' : CellInCapacity U c') : CellInCapacity U c := by
  exact h.2.trans hc'

/-- A cell inside a cell disjoint from `c'` is disjoint from `c'`. Blueprint 02 DEF-02. -/
theorem cellsDisjoint_of_cellSubset_left {c r c' : DyadicCell} (h : CellSubset c r)
    (hr : CellsDisjoint r c') : CellsDisjoint c c' := by
  rcases hr with hr | hr
  · exact Or.inl (h.2.trans hr)
  · exact Or.inr (hr.trans h.1)

/-- A cell lies inside `c'` exactly when `c'` is its ancestor at the depth of `c'`. -/
private theorem cellSubset_iff_ancestor {c c' : DyadicCell} :
    CellSubset c c' ↔ c'.1 ≤ c.1 ∧ c'.2 = c.2 / 2 ^ (c.1 - c'.1) := by
  constructor
  · intro h
    exact ⟨depth_le_of_cellSubset h, congrArg Prod.snd (cellAncestor_unique h)⟩
  · rintro ⟨hd, h2⟩
    have hc' : c' = cellAncestor c c'.1 := Prod.ext rfl h2
    rw [hc']
    exact cellSubset_cellAncestor c hd

/-- Cells are nonempty: a cell is never disjoint from a cell containing it. -/
private theorem not_cellsDisjoint_of_cellSubset {c c' : DyadicCell} (h : CellSubset c c') :
    ¬ CellsDisjoint c c' := by
  have hlt : cellLeft c < cellRight c := by
    have hlen := cellLength_eq_cellRight_sub_cellLeft c
    have hpos : 0 < cellLength c := by
      unfold cellLength
      positivity
    linarith
  rintro (hd | hd)
  · linarith [h.1]
  · linarith [h.2]

/-! ### The finite cell/cylinder correspondence -/

/-- Binary address of a cell inside `[0, 2^cap)`: the `depth + cap` big-endian bits of its
index. Blueprint 01 F1-CELL. -/
def cellAddress (cap : ℕ) (c : DyadicCell) : BitString := bitsOfNatBE (c.1 + cap) c.2

/-- The cell of depth `|w| - cap` addressed by a word `w` with `cap ≤ |w|`.
Blueprint 01 F1-CELL. -/
def cellOfAddress (cap : ℕ) (w : BitString) : DyadicCell := (w.length - cap, natOfBits w)

/-- A cell lies inside `[0, 2^cap)` exactly when its index is below `2^(depth + cap)`. -/
private theorem cellInCapacity_two_pow_iff {cap : ℕ} {c : DyadicCell} :
    CellInCapacity (2 ^ cap) c ↔ c.2 < 2 ^ (c.1 + cap) := by
  unfold CellInCapacity cellRight
  rw [div_le_iff₀ (by positivity), ← pow_add, add_comm cap c.1, Nat.lt_iff_add_one_le]
  norm_cast

/-- The first `m` bits of the `L`-bit code of `n` are the `m`-bit code of `n / 2^(L - m)`. -/
private theorem take_bitsOfNatBE {m L : ℕ} (n : ℕ) (hm : m ≤ L) :
    (bitsOfNatBE L n).take m = bitsOfNatBE m (n / 2 ^ (L - m)) := by
  unfold bitsOfNatBE
  rw [← List.map_take, List.take_range, min_eq_left hm]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [Nat.div_div_eq_div_mul, ← pow_add, show L - m + (m - 1 - i) = L - 1 - i by omega]

/-- The code of `n < 2^L` is a prefix of the code of `n' < 2^L'` exactly when `L ≤ L'` and `n`
is the leading part `n' / 2^(L' - L)` of `n'`. -/
private theorem bitsOfNatBE_prefix_iff {L L' n n' : ℕ} (hn : n < 2 ^ L) (hn' : n' < 2 ^ L') :
    bitsOfNatBE L n <+: bitsOfNatBE L' n' ↔ L ≤ L' ∧ n = n' / 2 ^ (L' - L) := by
  constructor
  · intro h
    have hL : L ≤ L' := by simpa using h.length_le
    refine ⟨hL, ?_⟩
    have hq : n' / 2 ^ (L' - L) < 2 ^ L := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_of_le hL]
      exact hn'
    rw [List.prefix_iff_eq_take, length_bitsOfNatBE, take_bitsOfNatBE n' hL] at h
    have hval := congrArg natOfBits h
    rwa [natOfBits_bitsOfNatBE hn, natOfBits_bitsOfNatBE hq] at hval
  · rintro ⟨hL, rfl⟩
    rw [← take_bitsOfNatBE n' hL]
    exact List.take_prefix _ _

/-- Decoding the address of a cell inside `[0, 2^cap)` returns the cell.
Blueprint 01 F1-CELL. -/
theorem cellOfAddress_cellAddress {cap : ℕ} {c : DyadicCell} (hc : CellInCapacity (2 ^ cap) c) :
    cellOfAddress cap (cellAddress cap c) = c := by
  rw [cellInCapacity_two_pow_iff] at hc
  simp [cellOfAddress, cellAddress, natOfBits_bitsOfNatBE hc]

/-- The cell addressed by a word of length `≥ cap` lies inside `[0, 2^cap)`.
Blueprint 01 F1-CELL. -/
theorem cellInCapacity_cellOfAddress {cap : ℕ} {w : BitString} (h : cap ≤ w.length) :
    CellInCapacity (2 ^ cap) (cellOfAddress cap w) := by
  rw [cellInCapacity_two_pow_iff]
  simp only [cellOfAddress, Nat.sub_add_cancel h]
  exact natOfBits_lt w

/-- The depth of the cell addressed by `w` is `|w| - cap`. Blueprint 01 F1-CELL. -/
theorem depth_cellOfAddress (cap : ℕ) (w : BitString) :
    (cellOfAddress cap w).1 = w.length - cap := by
  rfl

/-- Containment of cells inside `[0, 2^cap)` is the prefix relation of their addresses: `c`
lies inside `c'` exactly when the address of `c'` is a prefix of the address of `c`.
Blueprint 01 F1-CELL. -/
theorem cellSubset_iff_prefix_cellAddress {cap : ℕ} {c c' : DyadicCell}
    (hc : CellInCapacity (2 ^ cap) c) (hc' : CellInCapacity (2 ^ cap) c') :
    CellSubset c c' ↔ cellAddress cap c' <+: cellAddress cap c := by
  rw [cellInCapacity_two_pow_iff] at hc hc'
  simp only [cellAddress]
  rw [cellSubset_iff_ancestor, bitsOfNatBE_prefix_iff hc' hc, Nat.add_sub_add_right,
    Nat.add_le_add_iff_right]

/-- The exact finite correspondence of F1: two cells inside `[0, 2^cap)` are disjoint exactly
when their addresses are incomparable. Blueprint 01 F1-CELL. -/
theorem cellsDisjoint_iff_isIncomparable_cellAddress {cap : ℕ} {c c' : DyadicCell}
    (hc : CellInCapacity (2 ^ cap) c) (hc' : CellInCapacity (2 ^ cap) c') :
    CellsDisjoint c c' ↔ IsIncomparable (cellAddress cap c) (cellAddress cap c') := by
  unfold IsIncomparable
  rw [← cellSubset_iff_prefix_cellAddress hc' hc, ← cellSubset_iff_prefix_cellAddress hc hc']
  constructor
  · intro h
    exact ⟨fun hs => not_cellsDisjoint_of_cellSubset hs (Or.symm h),
      fun hs => not_cellsDisjoint_of_cellSubset hs h⟩
  · rintro ⟨h1, h2⟩
    rcases cellsDisjoint_or_cellSubset c c' with h | h | h
    · exact h
    · exact absurd h h2
    · exact absurd h h1

end Kolmogorov
