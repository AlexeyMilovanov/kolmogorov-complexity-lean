/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealApi

/-!
# Disjointifying a computable family of rational intervals

`IsEffectivelyNullReal` (`Omega/Basic.lean`) asks for covers whose *sum of lengths* is
small, while the Martin-Löf test of SUV p. 170 only bounds the *Lebesgue measure of the
union* of the enumerated intervals.  The two differ, and an enumeration cannot be pruned on
the fly, because an interval emitted early may only later become redundant.

This module closes the gap by a **grid** construction, a finite-combinatorial
argument that needs neither sorting nor a sweep-line merge.

Fix a computable family `I : ℕ → ℕ → Option (ℚ × ℚ)` of open rational intervals and a
level `n`.  Write `U_M := ⋃_{i < M} ratInterval (I n i)`.  At stage `N` consider the
*grid* `E_N` of all endpoints of `I n 0, …, I n N`, indexed by `t < 2(N+1)`: `gridEnd I n t`
is the left endpoint of `I n (t / 2)` when `t` is even and the right endpoint when `t` is
odd.  An *elementary cell* of the grid is an interval `(gridEnd t₁, gridEnd t₂)` that
contains no grid point in its interior (`gridGap`).  Because every `I n i` with `i ≤ N` has
both endpoints in the grid, a cell is **either contained in `I n i` or disjoint from it**
(`ratInterval_grid_dichotomy`) — so a cell is either contained in `U_M` or disjoint from
it, for every `M ≤ N + 1`, and its **midpoint decides which** (`gridCovered`).

`gridCover I n` enumerates the cells that are *new at their stage*: contained in `U_{N+1}`
but disjoint from `U_N`, with `t₁`, `t₂` chosen minimal among the indices carrying the same
rational value (`gridBefore`, which makes the enumeration injective).  These cells are

* **pairwise disjoint** (`gridCover_disjoint`) — inside one stage because two elementary
  cells of the same grid that overlap coincide, and across stages because a cell of stage
  `N` sits inside `U_{N+1}` while a cell of a later stage `N' > N` avoids `U_{N'} ⊇
  `U_{N+1}`;
* **inside the original union** (`iUnion_gridCover_subset`);
* and together they **cover every irrational point** of the union
  (`sdiff_range_ratCast_subset_iUnion_gridCover`): the least `N + 1` with `x ∈ U_{N+1}`
  gives a stage, and the largest grid point below `x` and the smallest above it bound the
  cell of that stage containing `x` (this is where irrationality of `x` is used: it
  guarantees that `x` is not itself a grid point).

The rationals that are missed are swept up separately by `isEffectivelyNullReal_range_ratCast`
in `Omega/NeighbourhoodCover.lean`, which is where the three theorems below are assembled
into `isEffectivelyNullReal_iInter_iUnion_of_volume_le`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The endpoint grid -/

/-- `gridEnd I n t` is the `t`-th endpoint of the level-`n` family: the left endpoint of
`I n (t / 2)` for even `t`, the right endpoint for odd `t`, and `0` when that interval is
absent. -/
def gridEnd (I : ℕ → ℕ → Option (ℚ × ℚ)) (n t : ℕ) : ℚ :=
  ((I n (t / 2)).map fun J => bif decide (t % 2 = 1) then J.2 else J.1).getD 0

/-- `gridValid I n t` says that the interval carrying the `t`-th endpoint is present. -/
def gridValid (I : ℕ → ℕ → Option (ℚ × ℚ)) (n t : ℕ) : Bool :=
  ((I n (t / 2)).map fun _ => true).getD false

/-- An endpoint index is valid exactly when the interval carrying it is present. -/
theorem gridValid_eq_true_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n t : ℕ) :
    gridValid I n t = true ↔ ∃ J, I n (t / 2) = some J := by
  cases h : I n (t / 2) with
  | none => simp [gridValid, h]
  | some J => simp [gridValid, h]

/-- The even endpoint index carries the left endpoint of its interval. -/
theorem gridEnd_two_mul {I : ℕ → ℕ → Option (ℚ × ℚ)} {n i : ℕ} {J : ℚ × ℚ}
    (h : I n i = some J) : gridEnd I n (2 * i) = J.1 := by
  have h1 : 2 * i / 2 = i := by omega
  have h2 : 2 * i % 2 = 0 := by omega
  simp [gridEnd, h1, h2, h]

/-- The odd endpoint index carries the right endpoint of its interval. -/
theorem gridEnd_two_mul_succ {I : ℕ → ℕ → Option (ℚ × ℚ)} {n i : ℕ} {J : ℚ × ℚ}
    (h : I n i = some J) : gridEnd I n (2 * i + 1) = J.2 := by
  have h1 : (2 * i + 1) / 2 = i := by omega
  have h2 : (2 * i + 1) % 2 = 1 := by omega
  simp [gridEnd, h1, h2, h]

/-- The even endpoint index of a present interval is valid. -/
theorem gridValid_two_mul {I : ℕ → ℕ → Option (ℚ × ℚ)} {n i : ℕ} {J : ℚ × ℚ}
    (h : I n i = some J) : gridValid I n (2 * i) = true := by
  have h1 : 2 * i / 2 = i := by omega
  simp [gridValid, h1, h]

/-- The odd endpoint index of a present interval is valid. -/
theorem gridValid_two_mul_succ {I : ℕ → ℕ → Option (ℚ × ℚ)} {n i : ℕ} {J : ℚ × ℚ}
    (h : I n i = some J) : gridValid I n (2 * i + 1) = true := by
  have h1 : (2 * i + 1) / 2 = i := by omega
  simp [gridValid, h1, h]

/-! ### Deciding membership of a rational -/

/-- `ratMemB I n i q` decides whether the rational `q` lies in the `i`-th interval of the
level-`n` family. -/
def ratMemB (I : ℕ → ℕ → Option (ℚ × ℚ)) (n i : ℕ) (q : ℚ) : Bool :=
  ((I n i).map fun J => decide (J.1 < q) && decide (q < J.2)).getD false

/-- The membership test is correct: it fires exactly when the rational lies in the interval. -/
theorem ratMemB_eq_true_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n i : ℕ) (q : ℚ) :
    ratMemB I n i q = true ↔ ((q : ℚ) : ℝ) ∈ (I n i).elim ∅ ratInterval := by
  cases h : I n i with
  | none => simp [ratMemB, h]
  | some J =>
      have hset : (Option.elim (some J) (∅ : Set ℝ) ratInterval)
          = Set.Ioo ((J.1 : ℚ) : ℝ) ((J.2 : ℚ) : ℝ) := rfl
      rw [hset]
      simp only [ratMemB, h, Option.map_some, Option.getD_some, Bool.and_eq_true,
        decide_eq_true_eq, Set.mem_Ioo]
      exact ⟨fun hq => ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩,
        fun hq => ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩⟩

/-! ### The three bounded searches -/

/-- `gridCovered I n q M` says that the rational `q` lies in one of `I n 0, …, I n (M-1)`. -/
def gridCovered (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (q : ℚ) : ℕ → Bool
  | 0 => false
  | M + 1 => gridCovered I n q M || ratMemB I n M q

/-- `gridGap I n a b B` says that no endpoint of index `< B` lies strictly inside `(a, b)`. -/
def gridGap (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (a b : ℚ) : ℕ → Bool
  | 0 => true
  | t + 1 => gridGap I n a b t &&
      !(gridValid I n t && decide (a < gridEnd I n t) && decide (gridEnd I n t < b))

/-- `gridBefore I n a t` says that no endpoint of index `< t` carries the value `a`; it makes
`t` the *canonical* index of the rational `a`. -/
def gridBefore (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (a : ℚ) : ℕ → Bool
  | 0 => true
  | s + 1 => gridBefore I n a s && !(gridValid I n s && decide (gridEnd I n s = a))

/-- `gridFirstEnd I n t` says that `t` is the *canonical* index of the rational it carries:
no smaller index carries the same value. -/
def gridFirstEnd (I : ℕ → ℕ → Option (ℚ × ℚ)) (n t : ℕ) : Bool :=
  gridBefore I n (gridEnd I n t) t

/-- The covering test fires exactly when the rational lies in one of the first `M` intervals. -/
theorem gridCovered_eq_true_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (q : ℚ) (M : ℕ) :
    gridCovered I n q M = true ↔ ∃ i, i < M ∧ ratMemB I n i q = true := by
  induction M with
  | zero => simp [gridCovered]
  | succ M ih =>
      simp only [gridCovered, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
        · exact ⟨M, Nat.lt_succ_self M, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
        · exact Or.inl ⟨i, hi', h⟩
        · exact Or.inr h

/-- The gap test fires exactly when no endpoint of index below `B` lies strictly between `a` and
`b`. -/
theorem gridGap_eq_true_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (a b : ℚ) (B : ℕ) :
    gridGap I n a b B = true ↔
      ∀ t, t < B → gridValid I n t = true → ¬(a < gridEnd I n t ∧ gridEnd I n t < b) := by
  induction B with
  | zero => simp [gridGap]
  | succ B ih =>
      simp only [gridGap, Bool.and_eq_true, Bool.not_eq_true', ih]
      constructor
      · rintro ⟨h1, h2⟩ t ht hv
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
        · exact h1 t ht' hv
        · intro hcon
          rw [hv] at h2
          simp only [Bool.true_and] at h2
          exact absurd h2 (by simp [hcon.1, hcon.2])
      · intro h
        refine ⟨fun t ht hv => h t (Nat.lt_succ_of_lt ht) hv, ?_⟩
        by_cases hv : gridValid I n B = true
        · have := h B (Nat.lt_succ_self B) hv
          rw [hv]
          simp only [Bool.true_and]
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases h1 : a < gridEnd I n B
          · exact Or.inr (fun h2 => this ⟨h1, h2⟩)
          · exact Or.inl h1
        · simp only [Bool.not_eq_true] at hv
          simp [hv]

/-- The novelty test fires exactly when no earlier endpoint carries the value `a`. -/
theorem gridBefore_eq_true_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) (a : ℚ) (t : ℕ) :
    gridBefore I n a t = true ↔
      ∀ s, s < t → gridValid I n s = true → gridEnd I n s ≠ a := by
  induction t with
  | zero => simp [gridBefore]
  | succ t ih =>
      simp only [gridBefore, Bool.and_eq_true, Bool.not_eq_true', ih]
      constructor
      · rintro ⟨h1, h2⟩ s hs hv
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs' | rfl
        · exact h1 s hs' hv
        · intro hcon
          rw [hv] at h2
          simp [hcon] at h2
      · intro h
        refine ⟨fun s hs hv => h s (Nat.lt_succ_of_lt hs) hv, ?_⟩
        by_cases hv : gridValid I n t = true
        · have := h t (Nat.lt_succ_self t) hv
          rw [hv]
          simp [this]
        · simp only [Bool.not_eq_true] at hv
          simp [hv]

/-- Two canonical indices carrying the same value coincide. -/
theorem gridBefore_unique {I : ℕ → ℕ → Option (ℚ × ℚ)} {n t₁ t₂ : ℕ} {a : ℚ}
    (h₁ : gridBefore I n a t₁ = true) (h₂ : gridBefore I n a t₂ = true)
    (hv₁ : gridValid I n t₁ = true) (hv₂ : gridValid I n t₂ = true)
    (he₁ : gridEnd I n t₁ = a) (he₂ : gridEnd I n t₂ = a) : t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd he₁ ((gridBefore_eq_true_iff I n a t₂).1 h₂ t₁ h hv₁)
  · exact h
  · exact absurd he₂ ((gridBefore_eq_true_iff I n a t₁).1 h₁ t₂ h hv₂)

/-! ### The dichotomy: an elementary cell is inside or outside each interval -/

/-- **The grid dichotomy.**  An interval `(a, b)` containing no endpoint of index
`< 2(N+1)` in its interior is, for each `i < N + 1`, either contained in `I n i` or
disjoint from it: both endpoints of `I n i` lie outside `(a, b)`. -/
theorem ratInterval_grid_dichotomy {I : ℕ → ℕ → Option (ℚ × ℚ)} {n N i : ℕ} {a b : ℚ}
    (hgap : gridGap I n a b (2 * (N + 1)) = true) (hi : i < N + 1) :
    Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) ⊆ (I n i).elim ∅ ratInterval
      ∨ Disjoint (Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ)) ((I n i).elim ∅ ratInterval) := by
  cases h : I n i with
  | none => exact Or.inr (by simp)
  | some J =>
      have hgap' := (gridGap_eq_true_iff I n a b (2 * (N + 1))).1 hgap
      have hlt1 : 2 * i < 2 * (N + 1) := by omega
      have hlt2 : 2 * i + 1 < 2 * (N + 1) := by omega
      have h1 : ¬(a < J.1 ∧ J.1 < b) := by
        have := hgap' (2 * i) hlt1 (gridValid_two_mul h)
        rwa [gridEnd_two_mul h] at this
      have h2 : ¬(a < J.2 ∧ J.2 < b) := by
        have := hgap' (2 * i + 1) hlt2 (gridValid_two_mul_succ h)
        rwa [gridEnd_two_mul_succ h] at this
      have hset : (Option.elim (some J) (∅ : Set ℝ) ratInterval)
          = Set.Ioo ((J.1 : ℚ) : ℝ) ((J.2 : ℚ) : ℝ) := rfl
      rw [hset]
      by_cases hb1 : b ≤ J.1
      · refine Or.inr (Set.disjoint_left.2 ?_)
        rintro x ⟨_, hxb⟩ ⟨hx1, _⟩
        have : ((b : ℚ) : ℝ) ≤ ((J.1 : ℚ) : ℝ) := by exact_mod_cast hb1
        linarith
      · push Not at hb1
        have hJ1a : J.1 ≤ a := by
          by_contra hcon
          push Not at hcon
          exact h1 ⟨hcon, hb1⟩
        by_cases hb2 : J.2 ≤ a
        · refine Or.inr (Set.disjoint_left.2 ?_)
          rintro x ⟨hxa, _⟩ ⟨_, hx2⟩
          have : ((J.2 : ℚ) : ℝ) ≤ ((a : ℚ) : ℝ) := by exact_mod_cast hb2
          linarith
        · push Not at hb2
          have hbJ2 : b ≤ J.2 := by
            by_contra hcon
            push Not at hcon
            exact h2 ⟨hb2, hcon⟩
          refine Or.inl (Set.Ioo_subset_Ioo ?_ ?_)
          · exact_mod_cast hJ1a
          · exact_mod_cast hbJ2

/-- The midpoint of a cell decides the dichotomy. -/
theorem mem_Ioo_mid {a b : ℚ} (h : a < b) :
    (((a + b) / 2 : ℚ) : ℝ) ∈ Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) := by
  have h' : ((a : ℚ) : ℝ) < ((b : ℚ) : ℝ) := by exact_mod_cast h
  constructor <;> · push_cast; linarith

/-- If the midpoint of a cell lies in `I n i`, the whole cell does. -/
theorem grid_cell_subset_of_mid {I : ℕ → ℕ → Option (ℚ × ℚ)} {n N i : ℕ} {a b : ℚ}
    (hgap : gridGap I n a b (2 * (N + 1)) = true) (hi : i < N + 1) (hab : a < b)
    (hmid : ratMemB I n i ((a + b) / 2) = true) :
    Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) ⊆ (I n i).elim ∅ ratInterval := by
  rcases ratInterval_grid_dichotomy hgap hi with h | h
  · exact h
  · exact absurd ((ratMemB_eq_true_iff I n i _).1 hmid)
      (Set.disjoint_left.1 h (mem_Ioo_mid hab))

/-- If the midpoint of a cell avoids `I n i`, the whole cell does. -/
theorem grid_cell_disjoint_of_mid {I : ℕ → ℕ → Option (ℚ × ℚ)} {n N i : ℕ} {a b : ℚ}
    (hgap : gridGap I n a b (2 * (N + 1)) = true) (hi : i < N + 1) (hab : a < b)
    (hmid : ratMemB I n i ((a + b) / 2) = false) :
    Disjoint (Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ)) ((I n i).elim ∅ ratInterval) := by
  rcases ratInterval_grid_dichotomy hgap hi with h | h
  · exact absurd ((ratMemB_eq_true_iff I n i _).2 (h (mem_Ioo_mid hab))) (by simp [hmid])
  · exact h

/-! ### The disjointified cover -/

/-- The cell test at stage `N`: `t₁` and `t₂` are canonical grid indices below
`2(N+1)`, they bound a nonempty interval containing no grid point, and that interval is new
at stage `N` — inside `U_{N+1}` but outside `U_N`, as decided by its midpoint. -/
def gridCellCond (I : ℕ → ℕ → Option (ℚ × ℚ)) (n N t₁ t₂ : ℕ) : Bool :=
  gridValid I n t₁ && gridValid I n t₂ &&
    decide (t₁ < 2 * (N + 1)) && decide (t₂ < 2 * (N + 1)) &&
    decide (gridEnd I n t₁ < gridEnd I n t₂) &&
    gridGap I n (gridEnd I n t₁) (gridEnd I n t₂) (2 * (N + 1)) &&
    gridFirstEnd I n t₁ &&
    gridFirstEnd I n t₂ &&
    gridCovered I n ((gridEnd I n t₁ + gridEnd I n t₂) / 2) (N + 1) &&
    !(gridCovered I n ((gridEnd I n t₁ + gridEnd I n t₂) / 2) N)

/-- **The disjointified cover.**  The index `k` decodes as `(N, t₁, t₂)` through `Nat.unpair`;
the cell is emitted exactly when `gridCellCond` holds. -/
def gridCover (I : ℕ → ℕ → Option (ℚ × ℚ)) (n k : ℕ) : Option (ℚ × ℚ) :=
  bif gridCellCond I n k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2 then
    some (gridEnd I n k.unpair.2.unpair.1, gridEnd I n k.unpair.2.unpair.2)
  else none

/-- Value of the disjointified cover at a paired index: the cell between two endpoints, present
exactly when the cell test fires. -/
theorem gridCover_pair (I : ℕ → ℕ → Option (ℚ × ℚ)) (n N t₁ t₂ : ℕ) :
    gridCover I n (Nat.pair N (Nat.pair t₁ t₂)) =
      bif gridCellCond I n N t₁ t₂ then some (gridEnd I n t₁, gridEnd I n t₂) else none := by
  simp [gridCover, Nat.unpair_pair]

/-- An interval of the disjointified cover comes from a firing cell test and has the two
endpoints as its endpoints. -/
theorem gridCover_eq_some {I : ℕ → ℕ → Option (ℚ × ℚ)} {n k : ℕ} {J : ℚ × ℚ}
    (h : gridCover I n k = some J) :
    gridCellCond I n k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2 = true ∧
      J = (gridEnd I n k.unpair.2.unpair.1, gridEnd I n k.unpair.2.unpair.2) := by
  by_cases hc : gridCellCond I n k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2 = true
  · rw [gridCover, hc] at h
    simp only [Bool.cond_true, Option.some.injEq] at h
    exact ⟨hc, h.symm⟩
  · simp only [Bool.not_eq_true] at hc
    rw [gridCover, hc] at h
    simp at h

/-- Unfolding of the cell test. -/
theorem gridCellCond_iff (I : ℕ → ℕ → Option (ℚ × ℚ)) (n N t₁ t₂ : ℕ) :
    gridCellCond I n N t₁ t₂ = true ↔
      gridValid I n t₁ = true ∧ gridValid I n t₂ = true ∧
      t₁ < 2 * (N + 1) ∧ t₂ < 2 * (N + 1) ∧
      gridEnd I n t₁ < gridEnd I n t₂ ∧
      gridGap I n (gridEnd I n t₁) (gridEnd I n t₂) (2 * (N + 1)) = true ∧
      gridBefore I n (gridEnd I n t₁) t₁ = true ∧
      gridBefore I n (gridEnd I n t₂) t₂ = true ∧
      gridCovered I n ((gridEnd I n t₁ + gridEnd I n t₂) / 2) (N + 1) = true ∧
      gridCovered I n ((gridEnd I n t₁ + gridEnd I n t₂) / 2) N = false := by
  simp only [gridCellCond, gridFirstEnd, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]
  tauto

/-! ### The three properties of `gridCover` -/

/-- Cells of the same stage that overlap are equal. -/
theorem gridCell_same_stage {I : ℕ → ℕ → Option (ℚ × ℚ)} {n N t₁ t₂ s₁ s₂ : ℕ}
    (h : gridCellCond I n N t₁ t₂ = true) (h' : gridCellCond I n N s₁ s₂ = true)
    (hne : ¬(gridEnd I n t₁ = gridEnd I n s₁ ∧ gridEnd I n t₂ = gridEnd I n s₂)) :
    Disjoint (Set.Ioo ((gridEnd I n t₁ : ℚ) : ℝ) ((gridEnd I n t₂ : ℚ) : ℝ))
      (Set.Ioo ((gridEnd I n s₁ : ℚ) : ℝ) ((gridEnd I n s₂ : ℚ) : ℝ)) := by
  obtain ⟨hv1, hv2, hb1, hb2, hab, hgap, -, -, -, -⟩ := (gridCellCond_iff I n N t₁ t₂).1 h
  obtain ⟨hw1, hw2, hc1, hc2, hcd, hgap', -, -, -, -⟩ := (gridCellCond_iff I n N s₁ s₂).1 h'
  set a := gridEnd I n t₁
  set b := gridEnd I n t₂
  set c := gridEnd I n s₁
  set d := gridEnd I n s₂
  refine Set.disjoint_left.2 ?_
  rintro x ⟨hxa, hxb⟩ ⟨hxc, hxd⟩
  have had : a < d := by
    have : ((a : ℚ) : ℝ) < ((d : ℚ) : ℝ) := lt_trans hxa hxd
    exact_mod_cast this
  have hcb : c < b := by
    have : ((c : ℚ) : ℝ) < ((b : ℚ) : ℝ) := lt_trans hxc hxb
    exact_mod_cast this
  have g1 := (gridGap_eq_true_iff I n a b (2 * (N + 1))).1 hgap
  have g2 := (gridGap_eq_true_iff I n c d (2 * (N + 1))).1 hgap'
  have hca : c ≤ a := by
    by_contra hcon
    push Not at hcon
    exact g1 s₁ hc1 hw1 ⟨hcon, hcb⟩
  have hac : a ≤ c := by
    by_contra hcon
    push Not at hcon
    exact g2 t₁ hb1 hv1 ⟨hcon, had⟩
  have hbd : b ≤ d := by
    by_contra hcon
    push Not at hcon
    exact g1 s₂ hc2 hw2 ⟨had, hcon⟩
  have hdb : d ≤ b := by
    by_contra hcon
    push Not at hcon
    exact g2 t₂ hb2 hv2 ⟨hcb, hcon⟩
  exact hne ⟨le_antisymm hac hca, le_antisymm hbd hdb⟩

/-- Cells of different stages are disjoint. -/
theorem gridCell_diff_stage {I : ℕ → ℕ → Option (ℚ × ℚ)} {n N N' t₁ t₂ s₁ s₂ : ℕ}
    (h : gridCellCond I n N t₁ t₂ = true) (h' : gridCellCond I n N' s₁ s₂ = true)
    (hNN : N < N') :
    Disjoint (Set.Ioo ((gridEnd I n t₁ : ℚ) : ℝ) ((gridEnd I n t₂ : ℚ) : ℝ))
      (Set.Ioo ((gridEnd I n s₁ : ℚ) : ℝ) ((gridEnd I n s₂ : ℚ) : ℝ)) := by
  obtain ⟨-, -, -, -, hab, hgap, -, -, hcov, -⟩ := (gridCellCond_iff I n N t₁ t₂).1 h
  obtain ⟨-, -, -, -, hcd, hgap', -, -, -, hncov⟩ := (gridCellCond_iff I n N' s₁ s₂).1 h'
  obtain ⟨i, hi, hmem⟩ := (gridCovered_eq_true_iff I n _ (N + 1)).1 hcov
  have hsub : Set.Ioo ((gridEnd I n t₁ : ℚ) : ℝ) ((gridEnd I n t₂ : ℚ) : ℝ)
      ⊆ (I n i).elim ∅ ratInterval := grid_cell_subset_of_mid hgap hi hab hmem
  have hiN' : i < N' := lt_of_lt_of_le hi hNN
  have hnot : ratMemB I n i ((gridEnd I n s₁ + gridEnd I n s₂) / 2) = false := by
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have : gridCovered I n ((gridEnd I n s₁ + gridEnd I n s₂) / 2) N' = true :=
      (gridCovered_eq_true_iff I n _ N').2 ⟨i, hiN', hcon⟩
    rw [hncov] at this
    exact absurd this (by simp)
  have hdisj : Disjoint (Set.Ioo ((gridEnd I n s₁ : ℚ) : ℝ) ((gridEnd I n s₂ : ℚ) : ℝ))
      ((I n i).elim ∅ ratInterval) :=
    grid_cell_disjoint_of_mid hgap' (Nat.lt_succ_of_lt hiN') hcd hnot
  exact (Set.disjoint_left.2 fun x hx hx' => (Set.disjoint_left.1 hdisj hx') (hsub hx))

/-- **The cover is pairwise disjoint.** -/
theorem gridCover_disjoint (I : ℕ → ℕ → Option (ℚ × ℚ)) (n k k' : ℕ) (hkk : k ≠ k') :
    Disjoint ((gridCover I n k).elim ∅ ratInterval)
      ((gridCover I n k').elim ∅ ratInterval) := by
  cases hk : gridCover I n k with
  | none => simp
  | some J =>
      cases hk' : gridCover I n k' with
      | none => simp
      | some J' =>
          obtain ⟨hc, hJ⟩ := gridCover_eq_some hk
          obtain ⟨hc', hJ'⟩ := gridCover_eq_some hk'
          have hsetJ : (Option.elim (some J) (∅ : Set ℝ) ratInterval)
              = Set.Ioo ((J.1 : ℚ) : ℝ) ((J.2 : ℚ) : ℝ) := rfl
          have hsetJ' : (Option.elim (some J') (∅ : Set ℝ) ratInterval)
              = Set.Ioo ((J'.1 : ℚ) : ℝ) ((J'.2 : ℚ) : ℝ) := rfl
          rw [hsetJ, hsetJ']
          subst hJ
          subst hJ'
          simp only
          rcases lt_trichotomy k.unpair.1 k'.unpair.1 with hN | hN | hN
          · exact gridCell_diff_stage hc hc' hN
          · rw [hN] at hc
            refine gridCell_same_stage hc hc' ?_
            rintro ⟨he1, he2⟩
            apply hkk
            obtain ⟨hv1, hv2, -, -, -, -, hbf1, hbf2, -, -⟩ :=
              (gridCellCond_iff I n k'.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2).1 hc
            obtain ⟨hw1, hw2, -, -, -, -, hbg1, hbg2, -, -⟩ :=
              (gridCellCond_iff I n k'.unpair.1 k'.unpair.2.unpair.1 k'.unpair.2.unpair.2).1 hc'
            have e1 : k.unpair.2.unpair.1 = k'.unpair.2.unpair.1 :=
              gridBefore_unique hbf1 (by rw [← he1] at hbg1; exact hbg1) hv1 hw1 rfl he1.symm
            have e2 : k.unpair.2.unpair.2 = k'.unpair.2.unpair.2 :=
              gridBefore_unique hbf2 (by rw [← he2] at hbg2; exact hbg2) hv2 hw2 rfl he2.symm
            have hp2 : k.unpair.2 = k'.unpair.2 := by
              rw [← Nat.pair_unpair k.unpair.2, ← Nat.pair_unpair k'.unpair.2, e1, e2]
            rw [← Nat.pair_unpair k, ← Nat.pair_unpair k', hN, hp2]
          · exact (gridCell_diff_stage hc' hc hN).symm

/-- **The cover stays inside the original union.** -/
theorem iUnion_gridCover_subset (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) :
    (⋃ k, (gridCover I n k).elim ∅ ratInterval) ⊆ ⋃ i, (I n i).elim ∅ ratInterval := by
  refine Set.iUnion_subset fun k => ?_
  cases hk : gridCover I n k with
  | none => simp
  | some J =>
      obtain ⟨hc, hJ⟩ := gridCover_eq_some hk
      obtain ⟨-, -, -, -, hab, hgap, -, -, hcov, -⟩ :=
        (gridCellCond_iff I n k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2).1 hc
      obtain ⟨i, hi, hmem⟩ := (gridCovered_eq_true_iff I n _ (k.unpair.1 + 1)).1 hcov
      have hsub := grid_cell_subset_of_mid hgap hi hab hmem
      have hsetJ : (Option.elim (some J) (∅ : Set ℝ) ratInterval)
          = Set.Ioo ((J.1 : ℚ) : ℝ) ((J.2 : ℚ) : ℝ) := rfl
      rw [hsetJ]
      subst hJ
      exact fun x hx => Set.mem_iUnion.2 ⟨i, hsub hx⟩

/-- **The cover catches every irrational point of the union.** -/
theorem sdiff_range_ratCast_subset_iUnion_gridCover (I : ℕ → ℕ → Option (ℚ × ℚ)) (n : ℕ) :
    (⋃ i, (I n i).elim ∅ ratInterval) \ Set.range ((↑) : ℚ → ℝ)
      ⊆ ⋃ k, (gridCover I n k).elim ∅ ratInterval := by
  classical
  rintro x ⟨hxU, hxirr⟩
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hxU
  -- the least stage at which `x` is covered
  have hex : ∃ M : ℕ, ∃ i, i < M ∧ x ∈ (I n i).elim ∅ ratInterval :=
    ⟨i₀ + 1, i₀, Nat.lt_succ_self i₀, hi₀⟩
  set M₀ := Nat.find hex with hM₀
  have hM₀spec : ∃ i, i < M₀ ∧ x ∈ (I n i).elim ∅ ratInterval := Nat.find_spec hex
  have hM₀ne : M₀ ≠ 0 := by
    intro h
    obtain ⟨i, hi, -⟩ := hM₀spec
    rw [h] at hi
    exact absurd hi (Nat.not_lt_zero i)
  obtain ⟨N, hN⟩ : ∃ N, M₀ = N + 1 := ⟨M₀ - 1, by omega⟩
  have hcov : ∃ i, i < N + 1 ∧ x ∈ (I n i).elim ∅ ratInterval := by rw [← hN]; exact hM₀spec
  have hncov : ¬∃ i, i < N ∧ x ∈ (I n i).elim ∅ ratInterval := by
    have : N < M₀ := by omega
    exact Nat.find_min hex this
  obtain ⟨iw, hiw, hxw⟩ := hcov
  obtain ⟨Jw, hJw⟩ : ∃ Jw, I n iw = some Jw := by
    cases h : I n iw with
    | none => rw [h] at hxw; simp at hxw
    | some Jw => exact ⟨Jw, rfl⟩
  have hxJw : ((Jw.1 : ℚ) : ℝ) < x ∧ x < ((Jw.2 : ℚ) : ℝ) := by
    rw [hJw] at hxw; exact hxw
  -- the grid of stage `N`
  set G : Finset ℚ :=
    ((Finset.range (2 * (N + 1))).filter fun t => gridValid I n t = true).image
      (gridEnd I n) with hG
  have hGmem : ∀ v : ℚ, v ∈ G ↔ ∃ t, t < 2 * (N + 1) ∧ gridValid I n t = true ∧
      gridEnd I n t = v := by
    intro v
    simp only [hG, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨t, ⟨ht, hv⟩, he⟩ => ⟨t, ht, hv, he⟩, fun ⟨t, ht, hv, he⟩ => ⟨t, ⟨ht, hv⟩, he⟩⟩
  have hJw1 : Jw.1 ∈ G := (hGmem _).2 ⟨2 * iw, by omega, gridValid_two_mul hJw,
    gridEnd_two_mul hJw⟩
  have hJw2 : Jw.2 ∈ G := (hGmem _).2 ⟨2 * iw + 1, by omega, gridValid_two_mul_succ hJw,
    gridEnd_two_mul_succ hJw⟩
  set Ga : Finset ℚ := G.filter fun v => ((v : ℚ) : ℝ) < x with hGa
  set Gb : Finset ℚ := G.filter fun v => x < ((v : ℚ) : ℝ) with hGb
  have hGaNe : Ga.Nonempty := ⟨Jw.1, by simp [hGa, hJw1, hxJw.1]⟩
  have hGbNe : Gb.Nonempty := ⟨Jw.2, by simp [hGb, hJw2, hxJw.2]⟩
  set a := Ga.max' hGaNe with ha
  set b := Gb.min' hGbNe with hb
  have haG : a ∈ Ga := Ga.max'_mem hGaNe
  have hbG : b ∈ Gb := Gb.min'_mem hGbNe
  have hax : ((a : ℚ) : ℝ) < x := by
    have := (Finset.mem_filter.1 haG).2
    exact this
  have hxb : x < ((b : ℚ) : ℝ) := by
    have := (Finset.mem_filter.1 hbG).2
    exact this
  have haGG : a ∈ G := (Finset.mem_filter.1 haG).1
  have hbGG : b ∈ G := (Finset.mem_filter.1 hbG).1
  have hab : a < b := by
    have : ((a : ℚ) : ℝ) < ((b : ℚ) : ℝ) := lt_trans hax hxb
    exact_mod_cast this
  -- no grid point strictly inside `(a, b)`
  have hgapG : ∀ v : ℚ, v ∈ G → ¬(a < v ∧ v < b) := by
    intro v hv ⟨hv1, hv2⟩
    have hvx : ((v : ℚ) : ℝ) ≠ x := fun h => hxirr ⟨v, h⟩
    rcases lt_or_gt_of_ne hvx with h | h
    · have : v ∈ Ga := Finset.mem_filter.2 ⟨hv, h⟩
      exact absurd (Ga.le_max' v this) (not_le.2 hv1)
    · have : v ∈ Gb := Finset.mem_filter.2 ⟨hv, h⟩
      exact absurd (Gb.min'_le v this) (not_le.2 hv2)
  have hgap : gridGap I n a b (2 * (N + 1)) = true := by
    refine (gridGap_eq_true_iff I n a b (2 * (N + 1))).2 fun t ht hvt => ?_
    exact hgapG (gridEnd I n t) ((hGmem _).2 ⟨t, ht, hvt, rfl⟩)
  -- canonical indices for `a` and `b`
  have hexa : ∃ t, gridValid I n t = true ∧ gridEnd I n t = a := by
    obtain ⟨t, -, hvt, het⟩ := (hGmem a).1 haGG
    exact ⟨t, hvt, het⟩
  have hexb : ∃ t, gridValid I n t = true ∧ gridEnd I n t = b := by
    obtain ⟨t, -, hvt, het⟩ := (hGmem b).1 hbGG
    exact ⟨t, hvt, het⟩
  set t₁ := Nat.find hexa with ht₁
  set t₂ := Nat.find hexb with ht₂
  obtain ⟨hv₁, he₁⟩ := Nat.find_spec hexa
  obtain ⟨hv₂, he₂⟩ := Nat.find_spec hexb
  have hbf₁ : gridBefore I n a t₁ = true := by
    refine (gridBefore_eq_true_iff I n a t₁).2 fun s hs hvs hcon => ?_
    exact Nat.find_min hexa hs ⟨hvs, hcon⟩
  have hbf₂ : gridBefore I n b t₂ = true := by
    refine (gridBefore_eq_true_iff I n b t₂).2 fun s hs hvs hcon => ?_
    exact Nat.find_min hexb hs ⟨hvs, hcon⟩
  have hlt₁ : t₁ < 2 * (N + 1) := by
    obtain ⟨t, ht, hvt, het⟩ := (hGmem a).1 haGG
    exact lt_of_le_of_lt (Nat.find_le ⟨hvt, het⟩) ht
  have hlt₂ : t₂ < 2 * (N + 1) := by
    obtain ⟨t, ht, hvt, het⟩ := (hGmem b).1 hbGG
    exact lt_of_le_of_lt (Nat.find_le ⟨hvt, het⟩) ht
  -- the midpoint conditions
  have hxIoo : x ∈ Set.Ioo ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) := ⟨hax, hxb⟩
  have hmidcov : gridCovered I n ((a + b) / 2) (N + 1) = true := by
    refine (gridCovered_eq_true_iff I n _ (N + 1)).2 ⟨iw, hiw, ?_⟩
    refine (ratMemB_eq_true_iff I n iw _).2 ?_
    rcases ratInterval_grid_dichotomy hgap hiw with h | h
    · exact h (mem_Ioo_mid hab)
    · exact absurd hxw (Set.disjoint_left.1 h hxIoo)
  have hmidncov : gridCovered I n ((a + b) / 2) N = false := by
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    obtain ⟨i, hi, hmem⟩ := (gridCovered_eq_true_iff I n _ N).1 hcon
    have hsub := grid_cell_subset_of_mid hgap (Nat.lt_succ_of_lt hi) hab hmem
    exact hncov ⟨i, hi, hsub hxIoo⟩
  -- assemble the cell
  have hcond : gridCellCond I n N t₁ t₂ = true := by
    refine (gridCellCond_iff I n N t₁ t₂).2 ?_
    rw [he₁, he₂]
    exact ⟨hv₁, hv₂, hlt₁, hlt₂, hab, hgap, hbf₁, hbf₂, hmidcov, hmidncov⟩
  refine Set.mem_iUnion.2 ⟨Nat.pair N (Nat.pair t₁ t₂), ?_⟩
  rw [gridCover_pair, hcond]
  simp only [Bool.cond_true]
  have hval : ((some (gridEnd I n t₁, gridEnd I n t₂) : Option (ℚ × ℚ)).elim ∅ ratInterval)
      = Set.Ioo ((gridEnd I n t₁ : ℚ) : ℝ) ((gridEnd I n t₂ : ℚ) : ℝ) := rfl
  rw [hval, he₁, he₂]
  exact hxIoo

/-! ### Computability -/

-- the `Computable` combinators unify against deeply projected tuples
/-- The endpoint function of a computable family is computable. -/
theorem computable_gridEnd {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable₂ (gridEnd I) := by
  have hdiv : Computable (fun p : ℕ × ℕ => p.2 / 2) :=
    (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)).to_comp
  have hI' : Computable (fun p : ℕ × ℕ => I p.1 (p.2 / 2)) := hI.comp Computable.fst hdiv
  have hmod : Computable (fun q : (ℕ × ℕ) × (ℚ × ℚ) => q.1.2 % 2) :=
    Primrec.nat_mod.to_comp.comp (Computable.snd.comp Computable.fst) (Computable.const 2)
  have hcond : Computable (fun q : (ℕ × ℕ) × (ℚ × ℚ) => decide (q.1.2 % 2 = 1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hmod (Computable.const 1)
  have hinner : Computable₂ (fun (p : ℕ × ℕ) (J : ℚ × ℚ) =>
      bif decide (p.2 % 2 = 1) then J.2 else J.1) :=
    Computable.cond hcond (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)
  exact Computable.option_getD (Computable.option_map hI' hinner) (Computable.const 0)

/-- The validity test of a computable family is computable. -/
theorem computable_gridValid {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable₂ (gridValid I) := by
  have hdiv : Computable (fun p : ℕ × ℕ => p.2 / 2) :=
    (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)).to_comp
  have hI' : Computable (fun p : ℕ × ℕ => I p.1 (p.2 / 2)) := hI.comp Computable.fst hdiv
  exact Computable.option_getD (Computable.option_map hI' (Computable.const true))
    (Computable.const false)

-- the `Computable` combinators unify against deeply projected tuples
/-- The membership test of a computable family is computable. -/
theorem computable_ratMemB {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable₂ (fun (p : ℕ × ℚ) (i : ℕ) => ratMemB I p.1 i p.2) := by
  have hI' : Computable (fun r : (ℕ × ℚ) × ℕ => I r.1.1 r.2) :=
    hI.comp (Computable.fst.comp Computable.fst) Computable.snd
  have h1 : Computable (fun q : ((ℕ × ℚ) × ℕ) × (ℚ × ℚ) => decide (q.2.1 < q.1.1.2)) :=
    computable₂_ratLt.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have h2 : Computable (fun q : ((ℕ × ℚ) × ℕ) × (ℚ × ℚ) => decide (q.1.1.2 < q.2.2)) :=
    computable₂_ratLt.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.snd)
  have hinner : Computable₂ (fun (r : (ℕ × ℚ) × ℕ) (J : ℚ × ℚ) =>
      decide (J.1 < r.1.2) && decide (r.1.2 < J.2)) := Primrec.and.to_comp.comp h1 h2
  exact Computable.option_getD (Computable.option_map hI' hinner) (Computable.const false)

-- the `Computable` combinators unify against deeply projected tuples
/-- The covering test of a computable family is computable. -/
theorem computable_gridCovered {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : (ℕ × ℚ) × ℕ => gridCovered I p.1.1 p.1.2 p.2) := by
  have hmem : Computable (fun r : ((ℕ × ℚ) × ℕ) × (ℕ × Bool) =>
      ratMemB I r.1.1.1 r.2.1 r.1.1.2) :=
    (computable_ratMemB hI).comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun (p : (ℕ × ℚ) × ℕ) (q : ℕ × Bool) =>
      q.2 || ratMemB I p.1.1 q.1 p.1.2) :=
    Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd) hmem
  refine (Computable.nat_rec Computable.snd (Computable.const false) hstep).of_eq fun p => ?_
  induction p.2 with
  | zero => rfl
  | succ M ih => simp only [gridCovered, ih]

-- the `Computable` combinators unify against deeply projected tuples
/-- The gap test of a computable family is computable. -/
theorem computable_gridGap {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : (ℕ × ℚ × ℚ) × ℕ => gridGap I p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hend : Computable (fun r : ((ℕ × ℚ × ℚ) × ℕ) × (ℕ × Bool) =>
      gridEnd I r.1.1.1 r.2.1) :=
    (computable_gridEnd hI).comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have hval : Computable (fun r : ((ℕ × ℚ × ℚ) × ℕ) × (ℕ × Bool) =>
      gridValid I r.1.1.1 r.2.1) :=
    (computable_gridValid hI).comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have hlt1 : Computable (fun r : ((ℕ × ℚ × ℚ) × ℕ) × (ℕ × Bool) =>
      decide (r.1.1.2.1 < gridEnd I r.1.1.1 r.2.1)) :=
    computable₂_ratLt.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))) hend
  have hlt2 : Computable (fun r : ((ℕ × ℚ × ℚ) × ℕ) × (ℕ × Bool) =>
      decide (gridEnd I r.1.1.1 r.2.1 < r.1.1.2.2)) :=
    computable₂_ratLt.comp hend
      (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
  have hstep : Computable₂ (fun (p : (ℕ × ℚ × ℚ) × ℕ) (q : ℕ × Bool) =>
      q.2 && !(gridValid I p.1.1 q.1 && decide (p.1.2.1 < gridEnd I p.1.1 q.1) &&
        decide (gridEnd I p.1.1 q.1 < p.1.2.2))) :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (Primrec.not.to_comp.comp
        (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hval hlt1) hlt2))
  refine (Computable.nat_rec Computable.snd (Computable.const true) hstep).of_eq fun p => ?_
  induction p.2 with
  | zero => rfl
  | succ B ih => simp only [gridGap, ih]

-- the `Computable` combinators unify against deeply projected tuples
/-- The novelty test of a computable family is computable. -/
theorem computable_gridBefore {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : (ℕ × ℚ) × ℕ => gridBefore I p.1.1 p.1.2 p.2) := by
  have hend : Computable (fun r : ((ℕ × ℚ) × ℕ) × (ℕ × Bool) => gridEnd I r.1.1.1 r.2.1) :=
    (computable_gridEnd hI).comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have hval : Computable (fun r : ((ℕ × ℚ) × ℕ) × (ℕ × Bool) => gridValid I r.1.1.1 r.2.1) :=
    (computable_gridValid hI).comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.fst.comp Computable.snd)
  have heq : Computable (fun r : ((ℕ × ℚ) × ℕ) × (ℕ × Bool) =>
      decide (gridEnd I r.1.1.1 r.2.1 = r.1.1.2)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hend
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hstep : Computable₂ (fun (p : (ℕ × ℚ) × ℕ) (q : ℕ × Bool) =>
      q.2 && !(gridValid I p.1.1 q.1 && decide (gridEnd I p.1.1 q.1 = p.1.2))) :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (Primrec.not.to_comp.comp (Primrec.and.to_comp.comp hval heq))
  refine (Computable.nat_rec Computable.snd (Computable.const true) hstep).of_eq fun p => ?_
  induction p.2 with
  | zero => rfl
  | succ t ih => simp only [gridBefore, ih]

/-- The stage component of a cover index. -/
private theorem computable_gridIdxStage : Computable (fun p : ℕ × ℕ => p.2.unpair.1) :=
  (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp

/-- The left-endpoint component of a cover index. -/
private theorem computable_gridIdxLeft : Computable (fun p : ℕ × ℕ => p.2.unpair.2.unpair.1) :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp Primrec.snd)))).to_comp

/-- The right-endpoint component of a cover index. -/
private theorem computable_gridIdxRight : Computable (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2) :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp Primrec.snd)))).to_comp

/-- The grid bound `2(N+1)` of a cover index. -/
private theorem computable_gridIdxBound : Computable (fun p : ℕ × ℕ => 2 * (p.2.unpair.1 + 1)) :=
  Primrec.nat_mul.to_comp.comp (Computable.const 2)
    (Computable.succ.comp computable_gridIdxStage)

/-- The left endpoint named by a cover index. -/
private theorem computable_gridIdxEndLeft {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ => gridEnd I p.1 p.2.unpair.2.unpair.1) :=
  (computable_gridEnd hI).comp Computable.fst computable_gridIdxLeft

/-- The right endpoint named by a cover index. -/
private theorem computable_gridIdxEndRight {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ => gridEnd I p.1 p.2.unpair.2.unpair.2) :=
  (computable_gridEnd hI).comp Computable.fst computable_gridIdxRight

/-- The midpoint of the cell named by a cover index. -/
private theorem computable_gridIdxMid {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ =>
      (gridEnd I p.1 p.2.unpair.2.unpair.1 + gridEnd I p.1 p.2.unpair.2.unpair.2) / 2) :=
  computable_ratHalf.comp
    (computable₂_ratAdd.comp (computable_gridIdxEndLeft hI) (computable_gridIdxEndRight hI))

/-- The tuple handed to `gridGap` by a cover index.  Naming it (with its type
written out) keeps the `Computable.pair` nest from being elaborated against a
metavariable-headed target, which is what made this proof expensive. -/
private theorem computable_gridIdxGapArg {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ =>
      (((p.1, (gridEnd I p.1 p.2.unpair.2.unpair.1, gridEnd I p.1 p.2.unpair.2.unpair.2)),
        2 * (p.2.unpair.1 + 1)) : (ℕ × ℚ × ℚ) × ℕ)) :=
  Computable.pair (Computable.pair Computable.fst
    (Computable.pair (computable_gridIdxEndLeft hI) (computable_gridIdxEndRight hI)))
    computable_gridIdxBound

/-- The gap test of the cell named by a cover index. -/
private theorem computable_gridIdxGap {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ => gridGap I p.1 (gridEnd I p.1 p.2.unpair.2.unpair.1)
      (gridEnd I p.1 p.2.unpair.2.unpair.2) (2 * (p.2.unpair.1 + 1))) :=
  ((computable_gridGap hI).comp (computable_gridIdxGapArg hI)).of_eq fun _ => rfl

-- the `Computable` combinators unify against deeply projected tuples
/-- Canonicity of an index. -/
theorem computable_gridFirstEnd {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable₂ (gridFirstEnd I) := by
  unfold gridFirstEnd
  exact (computable_gridBefore hI).comp
    (Computable.pair (Computable.pair Computable.fst (computable_gridEnd hI)) Computable.snd)

/-- Canonicity of a computable endpoint index of a cover index. -/
private theorem computable_gridIdxFirst {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I)
    {idx : ℕ × ℕ → ℕ} (hidx : Computable idx) :
    Computable (fun p : ℕ × ℕ => gridFirstEnd I p.1 (idx p)) :=
  (computable_gridFirstEnd hI).comp Computable.fst hidx

/-- The "covered at stage `N+1`" test of a cover index. -/
private theorem computable_gridIdxCovSucc {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ => gridCovered I p.1
      ((gridEnd I p.1 p.2.unpair.2.unpair.1 + gridEnd I p.1 p.2.unpair.2.unpair.2) / 2)
      (p.2.unpair.1 + 1)) := by
  have h := (computable_gridCovered hI).comp
    (Computable.pair (Computable.pair Computable.fst (computable_gridIdxMid hI))
      (Computable.succ.comp computable_gridIdxStage))
  exact h

/-- The "covered at stage `N`" test of a cover index. -/
private theorem computable_gridIdxCov {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ => gridCovered I p.1
      ((gridEnd I p.1 p.2.unpair.2.unpair.1 + gridEnd I p.1 p.2.unpair.2.unpair.2) / 2)
      p.2.unpair.1) :=
  (computable_gridCovered hI).comp
    (Computable.pair (Computable.pair Computable.fst (computable_gridIdxMid hI))
      computable_gridIdxStage)

-- the ten-fold `Bool`-conjunction chain of `gridCellCond`
/-- The cell test read off a cover index. -/
private theorem computable_gridIdxCond {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable (fun p : ℕ × ℕ =>
      gridCellCond I p.1 p.2.unpair.1 p.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2) := by
  have hv1 : Computable (fun p : ℕ × ℕ => gridValid I p.1 p.2.unpair.2.unpair.1) :=
    (computable_gridValid hI).comp Computable.fst computable_gridIdxLeft
  have hv2 : Computable (fun p : ℕ × ℕ => gridValid I p.1 p.2.unpair.2.unpair.2) :=
    (computable_gridValid hI).comp Computable.fst computable_gridIdxRight
  have hb1 : Computable (fun p : ℕ × ℕ =>
      decide (p.2.unpair.2.unpair.1 < 2 * (p.2.unpair.1 + 1))) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp computable_gridIdxLeft
      computable_gridIdxBound
  have hb2 : Computable (fun p : ℕ × ℕ =>
      decide (p.2.unpair.2.unpair.2 < 2 * (p.2.unpair.1 + 1))) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp computable_gridIdxRight
      computable_gridIdxBound
  have hord : Computable (fun p : ℕ × ℕ =>
      decide (gridEnd I p.1 p.2.unpair.2.unpair.1 < gridEnd I p.1 p.2.unpair.2.unpair.2)) :=
    computable₂_ratLt.comp (computable_gridIdxEndLeft hI) (computable_gridIdxEndRight hI)
  unfold gridCellCond
  exact Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp
        (Primrec.and.to_comp.comp
          (Primrec.and.to_comp.comp
            (Primrec.and.to_comp.comp
              (Primrec.and.to_comp.comp
                (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hv1 hv2) hb1) hb2)
              hord)
            (computable_gridIdxGap hI))
          (computable_gridIdxFirst hI computable_gridIdxLeft))
        (computable_gridIdxFirst hI computable_gridIdxRight))
      (computable_gridIdxCovSucc hI))
    (Primrec.not.to_comp.comp (computable_gridIdxCov hI))

/-- **The cover is computable.** -/
theorem computable₂_gridCover {I : ℕ → ℕ → Option (ℚ × ℚ)} (hI : Computable₂ I) :
    Computable₂ (gridCover I) := by
  unfold gridCover
  exact Computable.cond (computable_gridIdxCond hI)
    (Computable.option_some.comp
      (Computable.pair (computable_gridIdxEndLeft hI) (computable_gridIdxEndRight hI)))
    (Computable.const none)

end Kolmogorov
