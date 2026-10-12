import KolmogorovMathlib.StrongMerging.Lower.Cube
import Mathlib.Order.Partition.Finpartition

/-!
# The sharp lower bound: hypergeometric moments, sphere collisions and heavy cells

Blueprint nodes L07 (`hypergeometricMGF`), L08 (`sphereCollisionBound`) and L09
(`partitionHeavyBound`) of the formalization of `sublinear-merging.tex` (lemma
`lem:ham-collision`, tex lines 1276-1340; appendix, lines 4477-4505).

* **L07.**  Maclaurin's endpoint inequality `e_j(x) ≤ (n choose j) (mean x)^j` for nonnegative
  `x` (`esymmSum_le_choose_mul_mean_pow`, proved by finite smoothing), hence the hypergeometric
  moment bound `E a^J ≤ (1 - ρ + ρ a)^j` in both sampling directions
  (`hypergeometricMGF`, `hypergeometricMGF_dual`).
* **L08.**  `|S_u ∩ S_v| / N ≤ β^dist(u,v)` with `β = 2 √(ρ (1 - ρ))`, `ρ = R / M`, for
  `0 < R`, `2 R ≤ M`; no constant depends on `ρ`.
* **L09.**  The heavy-cell bound `eq:ham-heavy-bound`: for uniform `Z` and uniform `U ∈ S_Z`,
  `Pr[|P(U)| ≥ 2^ℓ, |P(U) ∩ S_Z| > 2^-δ |P(U)|] ≤ 2^δ (V(M, h-1) 2^-ℓ + β^h)`.  It is proved
  for an arbitrary cell assignment `u ↦ Q u` inside the cube (`partitionHeavyBound_of_cells`),
  which contains every finite partition of the cube (`partitionHeavyBound`).
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### L07: Maclaurin's inequality and the hypergeometric moment bound -/

/-- The elementary symmetric sum `e_j(x) = ∑_{S ⊆ X, |S| = j} ∏_{i ∈ S} x i`. -/
noncomputable def esymmSum {ι : Type*} (X : Finset ι) (x : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ S ∈ X.powersetCard j, ∏ i ∈ S, x i

/-- **Constant entries.**  If `x = c` on `X` then `e_j(x) = (|X| choose j) c^j`.

Proof sketch: every `S ∈ X.powersetCard j` has `∏_{i ∈ S} x i = c^|S| = c^j`
(`prod_congr`, `prod_const`, `mem_powersetCard`); then `sum_const` and `card_powersetCard`.
Reference: tex 1300-1306 (Maclaurin); node L07.  [leaf: easy] -/
theorem esymmSum_const {ι : Type*} (X : Finset ι) (x : ι → ℝ) (c : ℝ)
    (hx : ∀ i ∈ X, x i = c) (j : ℕ) : esymmSum X x j = (X.card.choose j : ℝ) * c ^ j := by
  unfold esymmSum
  calc ∑ S ∈ X.powersetCard j, ∏ i ∈ S, x i = ∑ _S ∈ X.powersetCard j, c ^ j := by
        refine Finset.sum_congr rfl fun S hS => ?_
        obtain ⟨hSX, hSc⟩ := Finset.mem_powersetCard.1 hS
        rw [Finset.prod_congr rfl fun i hi => hx i (hSX hi), Finset.prod_const, hSc]
    _ = (X.card.choose j : ℝ) * c ^ j := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- `e_0(x) = 1`. -/
theorem esymmSum_zero {ι : Type*} (X : Finset ι) (x : ι → ℝ) : esymmSum X x 0 = 1 := by
  simp [esymmSum]

/-- **One-element recursion**: `e_{j+1}(insert i Z) = e_{j+1}(Z) + x i e_j(Z)` for `i ∉ Z`.

Proof sketch: `Finset.powersetCard_succ_insert` splits the `(j+1)`-subsets of `insert i Z` into
those of `Z` and the image of `Z.powersetCard j` under `insert i`; the union is disjoint (the
latter contain `i`), `insert i` is injective on subsets of `Z` (`Finset.sum_union`,
`Finset.sum_image`), and `∏_{insert i S} x = x i ∏_S x` (`Finset.prod_insert`), then
`Finset.mul_sum`.
Reference: tex 1300-1306 (Maclaurin's inequality); node L07.  [leaf: medium] -/
theorem esymmSum_insert {ι : Type*} [DecidableEq ι] (Z : Finset ι) (x : ι → ℝ) {i : ι}
    (hi : i ∉ Z) (j : ℕ) :
    esymmSum (insert i Z) x (j + 1) = esymmSum Z x (j + 1) + x i * esymmSum Z x j := by
  unfold esymmSum
  have hdisj : Disjoint (Z.powersetCard (j + 1)) ((Z.powersetCard j).image (insert i)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.1 hS'
    exact hi ((Finset.mem_powersetCard.1 hS).1 (Finset.mem_insert_self i T))
  have hinj : Set.InjOn (insert i) (Z.powersetCard j : Set (Finset ι)) := by
    intro S hS T hT hST
    have hiS : i ∉ S := fun h => hi ((Finset.mem_powersetCard.1 hS).1 h)
    have hiT : i ∉ T := fun h => hi ((Finset.mem_powersetCard.1 hT).1 h)
    rw [← Finset.erase_insert hiS, ← Finset.erase_insert hiT]
    exact congrArg (fun U => Finset.erase U i) hST
  rw [Finset.powersetCard_succ_insert hi, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have hiS : i ∉ S := fun h => hi ((Finset.mem_powersetCard.1 hS).1 h)
  rw [Finset.prod_insert hiS]

/-- Elementary symmetric sums only depend on the entries in `Y`. -/
theorem esymmSum_congr {ι : Type*} (Y : Finset ι) {x y : ι → ℝ} (h : ∀ l ∈ Y, x l = y l)
    (j : ℕ) : esymmSum Y x j = esymmSum Y y j := by
  unfold esymmSum
  exact Finset.sum_congr rfl fun S hS =>
    Finset.prod_congr rfl fun l hl => h l ((Finset.mem_powersetCard.1 hS).1 hl)

/-- Elementary symmetric sums of nonnegative entries are nonnegative. -/
theorem esymmSum_nonneg {ι : Type*} (Y : Finset ι) {x : ι → ℝ} (h : ∀ l ∈ Y, 0 ≤ x l)
    (j : ℕ) : 0 ≤ esymmSum Y x j := by
  unfold esymmSum
  exact Finset.sum_nonneg fun S hS =>
    Finset.prod_nonneg fun l hl => h l ((Finset.mem_powersetCard.1 hS).1 hl)

/-- **Smoothing a pair increases every elementary symmetric sum.**  Let `i ≠ k` in `X`, and let
`y` agree with `x` on `X \ {i, k}`, with the same pair sum `x i + x k = y i + y k` and a larger
pair product `x i * x k ≤ y i * y k`, and `y ≥ 0` on `X`.  Then `e_j(x) ≤ e_j(y)`: with
`Y = X \ {i, k}`, `e_{j+2}(X) = e_{j+2}(Y) + (x i + x k) e_{j+1}(Y) + x i x k e_j(Y)`. -/
theorem esymmSum_le_of_smooth {ι : Type*} (X : Finset ι) (x y : ι → ℝ)
    (i k : ι) (hi : i ∈ X) (hk : k ∈ X) (hik : i ≠ k)
    (hy : ∀ l ∈ X, 0 ≤ y l) (hoff : ∀ l ∈ X, l ≠ i → l ≠ k → y l = x l)
    (hsum : x i + x k = y i + y k) (hprod : x i * x k ≤ y i * y k) (j : ℕ) :
    esymmSum X x j ≤ esymmSum X y j := by
  classical
  set Y := (X.erase i).erase k with hYdef
  have hYX : ∀ l ∈ Y, l ∈ X ∧ l ≠ i ∧ l ≠ k := by
    intro l hl
    simp only [hYdef, Finset.mem_erase] at hl
    exact ⟨hl.2.2, hl.2.1, hl.1⟩
  have hkY : k ∉ Y := fun h => (hYX k h).2.2 rfl
  have hiY : i ∉ insert k Y := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hik, fun h => (hYX i h).2.1 rfl⟩
  have hX : X = insert i (insert k Y) := by
    ext l
    simp only [hYdef, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hl
      by_cases h1 : l = i
      · exact Or.inl h1
      · by_cases h2 : l = k
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h2, h1, hl⟩)
    · rintro (h | h | ⟨_, _, hl⟩)
      · exact h ▸ hi
      · exact h ▸ hk
      · exact hl
  have hxy : ∀ m, esymmSum Y x m = esymmSum Y y m := fun m =>
    esymmSum_congr Y (fun l hl => (hoff l (hYX l hl).1 (hYX l hl).2.1 (hYX l hl).2.2).symm) m
  have hY0 : ∀ m, 0 ≤ esymmSum Y y m := fun m =>
    esymmSum_nonneg Y (fun l hl => hy l (hYX l hl).1) m
  rw [hX]
  cases j with
  | zero => simp [esymmSum_zero]
  | succ j =>
    cases j with
    | zero =>
      rw [esymmSum_insert _ _ hiY, esymmSum_insert _ _ hiY, esymmSum_insert _ _ hkY,
        esymmSum_insert _ _ hkY]
      simp only [esymmSum_zero, hxy]
      linarith
    | succ j =>
      rw [esymmSum_insert _ _ hiY, esymmSum_insert _ _ hiY, esymmSum_insert _ _ hkY,
        esymmSum_insert _ _ hkY, esymmSum_insert _ _ hkY, esymmSum_insert _ _ hkY]
      simp only [hxy]
      have e1 : (x i + x k) * esymmSum Y y (j + 1) = (y i + y k) * esymmSum Y y (j + 1) := by
        rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_right hprod (hY0 j), e1]

/-- **Entries on both sides of the mean.**  If some entry of `x` on `X` differs from the mean
`m`, then some entry is below `m` and some entry is above `m`.

Proof sketch: `X` is nonempty and `∑_{l ∈ X} (x l - m) = 0` (`Finset.sum_sub_distrib`,
`Finset.sum_const`, `nsmul_eq_mul`, `mul_div_cancel₀`).  If all `x l ≥ m`, the sum of the
nonnegative terms is `0`, so all are `0` (`Finset.sum_eq_zero_iff_of_nonneg`), contradicting
`hne`; symmetrically for `≤`.
Reference: tex 1300-1306 (Maclaurin); node L07.  [leaf: easy] -/
theorem exists_lt_and_gt_mean {ι : Type*} (X : Finset ι) (x : ι → ℝ)
    (hne : ∃ i ∈ X, x i ≠ (∑ k ∈ X, x k) / X.card) :
    (∃ i ∈ X, x i < (∑ k ∈ X, x k) / X.card) ∧ (∃ k ∈ X, (∑ l ∈ X, x l) / X.card < x k) := by
  obtain ⟨i0, hi0, hne0⟩ := hne
  have hcard : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hi0)
  set m := (∑ k ∈ X, x k) / X.card with hm
  have hsum : ∑ l ∈ X, (x l - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hm, mul_div_cancel₀ _ hcard,
      sub_self]
  constructor
  · by_contra h
    push Not at h
    have h0 : ∀ l ∈ X, 0 ≤ x l - m := fun l hl => sub_nonneg.2 (h l hl)
    have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 hsum i0 hi0
    exact hne0 (by linarith)
  · by_contra h
    push Not at h
    have h0 : ∀ l ∈ X, 0 ≤ m - x l := fun l hl => sub_nonneg.2 (h l hl)
    have hsum' : ∑ l ∈ X, (m - x l) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← hsum]
      exact Finset.sum_congr rfl fun l _ => neg_sub _ _
    have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 hsum' i0 hi0
    exact hne0 (by linarith)

/-- The smoothing of `x` at `i, k` towards the value `m`: `y i = m`, `y k = x i + x k - m`,
and `y = x` elsewhere. -/
noncomputable def smoothAt {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (i k : ι) (m : ℝ) :
    ι → ℝ :=
  fun l => if l = i then m else if l = k then x i + x k - m else x l

/-- **Smoothing preserves the sum** over `X ∋ i, k` (`i ≠ k`).

Proof sketch: write `X = insert i (insert k Y)` with `Y = (X.erase i).erase k`
(`Finset.insert_erase`), `Finset.sum_insert` twice, and `smoothAt = x` on `Y`
(`Finset.sum_congr`); then `m + (x i + x k - m) = x i + x k` (`ring`).
Reference: tex 1300-1306; node L07.  [leaf: easy] -/
theorem sum_smoothAt {ι : Type*} [DecidableEq ι] (X : Finset ι) (x : ι → ℝ) {i k : ι}
    (hi : i ∈ X) (hk : k ∈ X) (hik : i ≠ k) (m : ℝ) :
    ∑ l ∈ X, smoothAt x i k m l = ∑ l ∈ X, x l := by
  have hkX : k ∈ X.erase i := Finset.mem_erase.2 ⟨hik.symm, hk⟩
  rw [← Finset.add_sum_erase X (smoothAt x i k m) hi, ← Finset.add_sum_erase X x hi,
    ← Finset.add_sum_erase _ (smoothAt x i k m) hkX, ← Finset.add_sum_erase _ x hkX]
  have hrest : ∑ l ∈ (X.erase i).erase k, smoothAt x i k m l =
      ∑ l ∈ (X.erase i).erase k, x l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    obtain ⟨hlk, hl'⟩ := Finset.mem_erase.1 hl
    obtain ⟨hli, _⟩ := Finset.mem_erase.1 hl'
    simp [smoothAt, hli, hlk]
  have hyi : smoothAt x i k m i = m := by simp [smoothAt]
  have hyk : smoothAt x i k m k = x i + x k - m := by simp [smoothAt, hik.symm]
  rw [hrest, hyi, hyk]
  ring

/-- **Smoothing removes an off-mean entry.**  If `x i ≠ m` and `x k ≠ m` (`i ≠ k` in `X`), the
smoothed function has strictly fewer entries different from `m` on `X`.

Proof sketch: the off-mean set of `smoothAt x i k m` is contained in the off-mean set of `x`
minus `i` (`y i = m`; `y k` may or may not equal `m`, but `k` was already counted; other
entries are unchanged): `card_lt_card` with `Finset.filter_subset_filter`-type reasoning and
`i` in the old set but not the new one (`Finset.ssubset_iff_of_subset`).
Reference: tex 1300-1306; node L07.  [leaf: medium] -/
theorem card_filter_smoothAt_lt {ι : Type*} [DecidableEq ι] (X : Finset ι) (x : ι → ℝ)
    {i k : ι} (hi : i ∈ X) (hk : k ∈ X) (hik : i ≠ k) {m : ℝ} (hxi : x i ≠ m)
    (hxk : x k ≠ m) :
    (X.filter (fun l => smoothAt x i k m l ≠ m)).card < (X.filter (fun l => x l ≠ m)).card := by
  -- `hk`, `hik` are not needed: `k` is off the mean before and possibly after smoothing
  have _ : k ∈ X ∧ i ≠ k := ⟨hk, hik⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, Finset.mem_filter.2 ⟨hi, hxi⟩, fun h => ?_⟩
    have := (Finset.mem_filter.1 h).2
    simp [smoothAt] at this
  · intro l hl
    obtain ⟨hlX, hl⟩ := Finset.mem_filter.1 hl
    refine Finset.mem_filter.2 ⟨hlX, ?_⟩
    by_cases hli : l = i
    · rw [hli]
      exact hxi
    · by_cases hlk : l = k
      · rw [hlk]
        exact hxk
      · simpa [smoothAt, hli, hlk] using hl

/-- **One smoothing step.**  If the nonnegative `x` is not constant on `X` (some entry differs
from the mean `m`), there is a nonnegative `y` with the same sum, strictly fewer entries
different from the mean, and `e_j(x) ≤ e_j(y)` for every `j`: move an entry below the mean and
an entry above it to `m` and `x i + x k - m`. -/
theorem exists_smoothing {ι : Type*} (X : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ X, 0 ≤ x i) (hne : ∃ i ∈ X, x i ≠ (∑ k ∈ X, x k) / X.card) :
    ∃ y : ι → ℝ, (∀ i ∈ X, 0 ≤ y i) ∧ ∑ k ∈ X, y k = ∑ k ∈ X, x k ∧
      (X.filter (fun i => y i ≠ (∑ k ∈ X, y k) / X.card)).card <
        (X.filter (fun i => x i ≠ (∑ k ∈ X, x k) / X.card)).card ∧
      ∀ j, esymmSum X x j ≤ esymmSum X y j := by
  classical
  obtain ⟨⟨i, hi, hxi⟩, ⟨k, hk, hxk⟩⟩ := exists_lt_and_gt_mean X x hne
  set m := (∑ l ∈ X, x l) / X.card with hm
  have hik : i ≠ k := by
    rintro rfl
    linarith
  have hm0 : 0 ≤ m := div_nonneg (Finset.sum_nonneg hx) (Nat.cast_nonneg _)
  have hyi : smoothAt x i k m i = m := by simp [smoothAt]
  have hyk : smoothAt x i k m k = x i + x k - m := by simp [smoothAt, hik.symm]
  have hy0 : ∀ l ∈ X, 0 ≤ smoothAt x i k m l := by
    intro l hl
    unfold smoothAt
    split_ifs
    · exact hm0
    · linarith [hx i hi]
    · exact hx l hl
  have hsum := sum_smoothAt X x hi hk hik m
  refine ⟨smoothAt x i k m, hy0, hsum, ?_, fun j => ?_⟩
  · rw [hsum]
    exact card_filter_smoothAt_lt X x hi hk hik hxi.ne hxk.ne'
  · refine esymmSum_le_of_smooth X x _ i k hi hk hik hy0
      (fun l _ hli hlk => by simp [smoothAt, hli, hlk]) ?_ ?_ j
    · rw [hyi, hyk]
      ring
    · rw [hyi, hyk]
      nlinarith [mul_pos (sub_pos.2 hxi) (sub_pos.2 hxk)]

/-- **Maclaurin's endpoint inequality** for elementary symmetric means: for nonnegative `x` on
`X`, `e_j(x) ≤ (|X| choose j) (∑_{i ∈ X} x i / |X|)^j`.  Proved by strong induction on the
number of entries different from the mean, using `exists_smoothing` and `esymmSum_const`. -/
theorem esymmSum_le_choose_mul_mean_pow {ι : Type*} (X : Finset ι) (j : ℕ)
    (x : ι → ℝ) (hx : ∀ i ∈ X, 0 ≤ x i) :
    esymmSum X x j ≤ (X.card.choose j : ℝ) * ((∑ i ∈ X, x i) / X.card) ^ j := by
  suffices H : ∀ n : ℕ, ∀ x : ι → ℝ, (∀ i ∈ X, 0 ≤ x i) →
      (X.filter (fun i => x i ≠ (∑ k ∈ X, x k) / X.card)).card = n →
      esymmSum X x j ≤ (X.card.choose j : ℝ) * ((∑ i ∈ X, x i) / X.card) ^ j from
    H _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    by_cases hall : ∀ i ∈ X, x i = (∑ k ∈ X, x k) / X.card
    · exact (esymmSum_const X x _ hall j).le
    · push Not at hall
      obtain ⟨y, hy0, hysum, hycount, hxy⟩ := exists_smoothing X x hx hall
      have hy := ih (X.filter (fun i => y i ≠ (∑ k ∈ X, y k) / X.card)).card
        (lt_of_lt_of_eq hycount hn) y hy0 rfl
      rw [hysum] at hy
      exact (hxy j).trans hy

/-- **Two-valued products.**  `∏_{i ∈ S} (if i ∈ A then a else 1) = a^|S ∩ A|`.

Proof sketch: `prod_ite`, `prod_const`, `prod_const_one`, and `filter_mem_eq_inter`.
Reference: tex 1304-1306; node L07.  [leaf: easy] -/
theorem prod_ite_mem_eq_pow {ι : Type*} [DecidableEq ι] (S A : Finset ι) (a : ℝ) :
    ∏ i ∈ S, (if i ∈ A then a else 1) = a ^ (S ∩ A).card := by
  rw [Finset.prod_ite_mem, Finset.prod_const]

/-- **Mean of the two-valued list.**  For `A ⊆ X` with `X` nonempty, the mean of the list with
`|A|` copies of `a` and `|X| - |A|` copies of `1` is `1 - ρ + ρ a`, `ρ = |A| / |X|`.

Proof sketch: `sum_ite_mem`/`sum_ite`: the sum is `|A| a + (|X| - |A|)` (`card_sdiff`,
`Nat.cast_sub`); divide by `|X| > 0` (`field_simp`, `ring`).
Reference: tex 1304-1306; node L07.  [leaf: easy] -/
theorem mean_ite_mem {ι : Type*} [DecidableEq ι] (X A : Finset ι) (hAX : A ⊆ X)
    (hX : 0 < X.card) (a : ℝ) :
    (∑ i ∈ X, (if i ∈ A then a else 1)) / X.card =
      1 - (A.card : ℝ) / X.card + (A.card : ℝ) / X.card * a := by
  have hsum : ∑ i ∈ X, (if i ∈ A then a else 1) = X.card + A.card * (a - 1) := by
    have h1 : ∀ i ∈ X, (if i ∈ A then a else 1) = 1 + (if i ∈ A then a - 1 else 0) := by
      intro i _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 hAX, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
      nsmul_eq_mul, mul_one]
  have hX' : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hX.ne'
  rw [hsum]
  field_simp
  ring

/-- **Hypergeometric moment bound** (blueprint node L07).  Sample `j` positions of a population
`X` of size `M > 0` containing `R = |A|` marked ones; the number `J = |S ∩ A|` of marked
positions satisfies `E a^J ≤ (1 - ρ + ρ a)^j` with `ρ = R / M`, for every `a ≥ 0` and every `j`
(written with the sum over all `j`-subsets, i.e. multiplied by `(M choose j)`). -/
theorem hypergeometricMGF {ι : Type*} [DecidableEq ι] (X A : Finset ι) (hAX : A ⊆ X)
    (hX : 0 < X.card) {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∑ S ∈ X.powersetCard j, a ^ (S ∩ A).card ≤
      (X.card.choose j : ℝ) * (1 - (A.card : ℝ) / X.card + (A.card : ℝ) / X.card * a) ^ j := by
  have hx : ∀ i ∈ X, (0 : ℝ) ≤ (if i ∈ A then a else 1) := fun i _ => by
    split_ifs
    · exact ha
    · exact zero_le_one
  have h : esymmSum X (fun i => if i ∈ A then a else 1) j ≤ (X.card.choose j : ℝ) *
      ((∑ i ∈ X, (if i ∈ A then a else 1)) / X.card) ^ j :=
    esymmSum_le_choose_mul_mean_pow X j _ hx
  rw [mean_ite_mem X A hAX hX a] at h
  calc ∑ S ∈ X.powersetCard j, a ^ (S ∩ A).card
      = esymmSum X (fun i => if i ∈ A then a else 1) j :=
        Finset.sum_congr rfl fun S _ => (prod_ite_mem_eq_pow S A a).symm
    _ ≤ _ := h

/-- The `R`-subsets of `X` meeting `D ⊆ X` in exactly `i ≤ R` points number
`(|D| choose i) ((|X| - |D|) choose (R - i))`. -/
private theorem sum_powersetCard_pow_card_inter_aux {ι : Type*} [DecidableEq ι]
    (X D : Finset ι) (hDX : D ⊆ X) {R i : ℕ} (hiR : i ≤ R) :
    ((X.powersetCard R).filter (fun F => (F ∩ D).card = i)).card =
      D.card.choose i * (X.card - D.card).choose (R - i) := by
  rw [← Finset.card_sdiff_of_subset hDX, ← Finset.card_powersetCard,
    ← Finset.card_powersetCard, ← Finset.card_product]
  have hQD : ∀ Q ∈ (X \ D).powersetCard (R - i), ∀ x ∈ Q, x ∉ D := fun Q hQ x hx =>
    (Finset.mem_sdiff.1 ((Finset.mem_powersetCard.1 hQ).1 hx)).2
  have hinter : ∀ P ∈ D.powersetCard i, ∀ Q ∈ (X \ D).powersetCard (R - i),
      (P ∪ Q) ∩ D = P := by
    intro P hP Q hQ
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxD⟩
      · exact hx
      · exact absurd hxD (hQD Q hQ x hx)
    · intro hx
      exact ⟨Or.inl hx, (Finset.mem_powersetCard.1 hP).1 hx⟩
  refine Finset.card_nbij' (fun F => (F ∩ D, F \ D)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro F hF
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hF
    obtain ⟨⟨hFX, hFR⟩, hFD⟩ := hF
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨Finset.inter_subset_right, hFD⟩, ⟨Finset.sdiff_subset_sdiff hFX subset_rfl, ?_⟩⟩
    change (F \ D).card = R - i
    have := Finset.card_sdiff_add_card_inter F D
    omega
  · rintro ⟨P, Q⟩ hPQ
    rw [Finset.mem_coe, Finset.mem_product] at hPQ
    obtain ⟨hP, hQ⟩ := hPQ
    obtain ⟨hPD, hPi⟩ := Finset.mem_powersetCard.1 hP
    obtain ⟨hQXD, hQR⟩ := Finset.mem_powersetCard.1 hQ
    have hdisj : Disjoint P Q :=
      Finset.disjoint_left.2 fun x hxP hxQ => hQD Q hQ x hxQ (hPD hxP)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard, hinter P hP Q hQ,
      Finset.card_union_of_disjoint hdisj, hPi, hQR]
    exact ⟨⟨Finset.union_subset (hPD.trans hDX) (hQXD.trans Finset.sdiff_subset), by omega⟩,
      rfl⟩
  · intro F _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · rintro ⟨P, Q⟩ hPQ
    rw [Finset.mem_coe, Finset.mem_product] at hPQ
    obtain ⟨hP, hQ⟩ := hPQ
    have hPD := (Finset.mem_powersetCard.1 hP).1
    refine Prod.ext (hinter P hP Q hQ) ?_
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxD⟩
      · exact absurd (hPD hx) hxD
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hQD Q hQ x hx⟩

/-- **Counting samples by the intersection size.**  For `D ⊆ X`,
`∑_{F ⊆ X, |F| = R} a^|F ∩ D| = ∑_{i ≤ R} (|D| choose i) ((|X| - |D|) choose (R - i)) a^i`.

Proof sketch: group by `i = |F ∩ D| ≤ R` (`Finset.sum_fiberwise_of_maps_to`,
`card_le_card inter_subset_left`); for `i ≤ R`, `F ↦ (F ∩ D, F \ D)` is a bijection from
`{F ⊆ X : |F| = R, |F ∩ D| = i}` onto `D.powersetCard i ×ˢ (X \ D).powersetCard (R - i)`
(inverse `(P, Q) ↦ P ∪ Q`), so its size is `(|D| choose i) ((|X| - |D|) choose (R - i))`
(`card_powersetCard`, `card_sdiff`).
Reference: tex 1296-1300 (hypergeometric law); node L07.  [leaf: medium] -/
theorem sum_powersetCard_pow_card_inter {ι : Type*} [DecidableEq ι] (X D : Finset ι)
    (hDX : D ⊆ X) (R : ℕ) (a : ℝ) :
    ∑ F ∈ X.powersetCard R, a ^ (F ∩ D).card =
      ∑ i ∈ range (R + 1), (D.card.choose i * (X.card - D.card).choose (R - i) : ℝ) * a ^ i := by
  have hmaps : ∀ F ∈ X.powersetCard R, (F ∩ D).card ∈ range (R + 1) := by
    intro F hF
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.card_le_card Finset.inter_subset_left).trans
      (Finset.mem_powersetCard.1 hF).2.le
  calc ∑ F ∈ X.powersetCard R, a ^ (F ∩ D).card
      = ∑ i ∈ range (R + 1), ∑ F ∈ (X.powersetCard R).filter (fun F => (F ∩ D).card = i),
          a ^ (F ∩ D).card := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiR : i ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hconst : ∑ F ∈ (X.powersetCard R).filter (fun F => (F ∩ D).card = i),
          a ^ (F ∩ D).card =
            ∑ _F ∈ (X.powersetCard R).filter (fun F => (F ∩ D).card = i), a ^ i :=
        Finset.sum_congr rfl fun F hF => by rw [(Finset.mem_filter.1 hF).2]
      rw [hconst, Finset.sum_const, nsmul_eq_mul,
        sum_powersetCard_pow_card_inter_aux X D hDX hiR]
      push_cast
      ring

/-- **Termwise binomial symmetry**: for `i ≤ R`, `i ≤ j` and `j, R ≤ M`,
`(M choose j)(j choose i)((M-j) choose (R-i)) = (M choose R)(R choose i)((M-R) choose (j-i))`
(the natural subtractions are genuine here).

Proof sketch: `Nat.choose_mul` turns both sides into `(M choose i)` times
`((M-i) choose (j-i)) ((M-j) choose (R-i))`, resp. `((M-i) choose (R-i)) ((M-R) choose (j-i))`;
with `N = M - i`, `a = j - i`, `b = R - i` this is
`(N choose a)((N-a) choose b) = (N choose b)((N-b) choose a)` (both count pairs of disjoint
subsets of sizes `a`, `b`; e.g. `Nat.choose_mul` with `Nat.add_choose_mul`-type rewriting, or
cast to `ℚ` and use `Nat.cast_choose` when `a + b ≤ N`, both sides `0` otherwise).
Reference: tex 1296-1300; node L07.  [leaf: medium] -/
theorem choose_mul_choose_mul_choose_symm {M j R i : ℕ} (hiR : i ≤ R) (hij : i ≤ j)
    (hj : j ≤ M) (hR : R ≤ M) :
    M.choose j * j.choose i * (M - j).choose (R - i) =
      M.choose R * R.choose i * (M - R).choose (j - i) := by
  rw [Nat.choose_mul hij, Nat.choose_mul hiR, mul_assoc, mul_assoc]
  congr 1
  have hMj : M - j = (M - i) - (j - i) := by omega
  have hMR : M - R = (M - i) - (R - i) := by omega
  rw [hMj, hMR]
  have key : ∀ N a b : ℕ, a ≤ N → b ≤ N →
      N.choose a * (N - a).choose b = N.choose b * (N - b).choose a := by
    intro N a b ha hb
    by_cases hab : a + b ≤ N
    · have e1 := Nat.choose_mul (n := N) (k := a + b) (s := a) (Nat.le_add_right a b)
      have e2 := Nat.choose_mul (n := N) (k := a + b) (s := b) (Nat.le_add_left b a)
      rw [Nat.add_sub_cancel_left] at e1
      rw [Nat.add_sub_cancel] at e2
      rw [← e1, ← e2, Nat.choose_symm_add]
    · push Not at hab
      rw [Nat.choose_eq_zero_of_lt (by omega : N - a < b),
        Nat.choose_eq_zero_of_lt (by omega : N - b < a), mul_zero, mul_zero]
  exact key _ _ _ (by omega) (by omega)

/-- **Binomial symmetry of the hypergeometric weights.**  For `j, R ≤ M`,
`(M choose j) ∑_{i ≤ R} (j choose i) ((M-j) choose (R-i)) a^i =
(M choose R) ∑_{i ≤ j} (R choose i) ((M-R) choose (j-i)) a^i`: both sums reduce to
`i ≤ min R j` (the other terms vanish), where they agree termwise. -/
theorem choose_mul_sum_hypergeom_symm (M j R : ℕ) (hj : j ≤ M) (hR : R ≤ M) (a : ℝ) :
    (M.choose j : ℝ) * ∑ i ∈ range (R + 1), (j.choose i * (M - j).choose (R - i) : ℝ) * a ^ i =
      (M.choose R : ℝ) *
        ∑ i ∈ range (j + 1), (R.choose i * (M - R).choose (j - i) : ℝ) * a ^ i := by
  have hL : ∑ i ∈ range (R + 1), (j.choose i * (M - j).choose (R - i) : ℝ) * a ^ i =
      ∑ i ∈ range (min R j + 1), (j.choose i * (M - j).choose (R - i) : ℝ) * a ^ i := by
    refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)).symm
    · simp only [Finset.mem_range] at hi ⊢
      omega
    · simp only [Finset.mem_range] at hi hi'
      have hji : j < i := by omega
      simp [Nat.choose_eq_zero_of_lt hji]
  have hR' : ∑ i ∈ range (j + 1), (R.choose i * (M - R).choose (j - i) : ℝ) * a ^ i =
      ∑ i ∈ range (min R j + 1), (R.choose i * (M - R).choose (j - i) : ℝ) * a ^ i := by
    refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)).symm
    · simp only [Finset.mem_range] at hi ⊢
      omega
    · simp only [Finset.mem_range] at hi hi'
      have hRi : R < i := by omega
      simp [Nat.choose_eq_zero_of_lt hRi]
  rw [hL, hR', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have key := choose_mul_choose_mul_choose_symm (M := M) (j := j) (R := R) (i := i)
    (by omega) (by omega) hj hR
  have key' : ((M.choose j * j.choose i * (M - j).choose (R - i) : ℕ) : ℝ) =
      ((M.choose R * R.choose i * (M - R).choose (j - i) : ℕ) : ℝ) := by
    rw [key]
  push_cast at key'
  calc (M.choose j : ℝ) * ((j.choose i * (M - j).choose (R - i) : ℝ) * a ^ i)
      = ((M.choose j : ℝ) * j.choose i * (M - j).choose (R - i)) * a ^ i := by ring
    _ = ((M.choose R : ℝ) * R.choose i * (M - R).choose (j - i)) * a ^ i := by rw [key']
    _ = (M.choose R : ℝ) * ((R.choose i * (M - R).choose (j - i) : ℝ) * a ^ i) := by ring

/-- **Symmetry of the hypergeometric law.**  For `A, D ⊆ X`, sampling `|A|` positions and
counting those in `D`, or sampling `|D|` positions and counting those in `A`, give the same law:
`(M choose |D|) ∑_{|F| = |A|} a^|F ∩ D| = (M choose |A|) ∑_{|G| = |D|} a^|G ∩ A|`, `M = |X|`. -/
theorem choose_mul_sum_pow_inter_symm {ι : Type*} [DecidableEq ι] (X A D : Finset ι)
    (hAX : A ⊆ X) (hDX : D ⊆ X) (a : ℝ) :
    (X.card.choose D.card : ℝ) * ∑ F ∈ X.powersetCard A.card, a ^ (F ∩ D).card =
      (X.card.choose A.card : ℝ) * ∑ G ∈ X.powersetCard D.card, a ^ (G ∩ A).card := by
  rw [sum_powersetCard_pow_card_inter X D hDX A.card a,
    sum_powersetCard_pow_card_inter X A hAX D.card a]
  exact choose_mul_sum_hypergeom_symm X.card D.card A.card (card_le_card hDX)
    (card_le_card hAX) a

/-- **Hypergeometric moment bound, dual sampling** (blueprint node L07, the form used for
sphere collisions): for `D ⊆ X`, `R ≤ |X| = M`, `M > 0` and `a ≥ 0`,
`∑_{F ⊆ X, |F| = R} a^|F ∩ D| ≤ (M choose R) (1 - ρ + ρ a)^|D|` with `ρ = R / M`. -/
theorem hypergeometricMGF_dual {ι : Type*} [DecidableEq ι] (X D : Finset ι) (hDX : D ⊆ X)
    (R : ℕ) (hR : R ≤ X.card) (hX : 0 < X.card) {a : ℝ} (ha : 0 ≤ a) :
    ∑ F ∈ X.powersetCard R, a ^ (F ∩ D).card ≤
      (X.card.choose R : ℝ) * (1 - (R : ℝ) / X.card + (R : ℝ) / X.card * a) ^ D.card := by
  obtain ⟨A, hAX, hAcard⟩ := Finset.exists_subset_card_eq hR
  have hsymm := choose_mul_sum_pow_inter_symm X A D hAX hDX a
  have hmgf := hypergeometricMGF X A hAX hX ha D.card
  rw [hAcard] at hsymm hmgf
  have hpos : (0 : ℝ) < X.card.choose D.card := by
    exact_mod_cast Nat.choose_pos (Finset.card_le_card hDX)
  have key : (X.card.choose D.card : ℝ) * ∑ F ∈ X.powersetCard R, a ^ (F ∩ D).card ≤
      (X.card.choose D.card : ℝ) * ((X.card.choose R : ℝ) *
        (1 - (R : ℝ) / X.card + (R : ℝ) / X.card * a) ^ D.card) := by
    rw [hsymm]
    calc (X.card.choose R : ℝ) * ∑ G ∈ X.powersetCard D.card, a ^ (G ∩ A).card
        ≤ (X.card.choose R : ℝ) * ((X.card.choose D.card : ℝ) *
            (1 - (R : ℝ) / X.card + (R : ℝ) / X.card * a) ^ D.card) :=
          mul_le_mul_of_nonneg_left hmgf (Nat.cast_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hpos

/-! ### L08: exact-sphere collisions -/

/-- The collision factor `β = 2 √(ρ (1 - ρ))` with `ρ = R / M`. -/
noncomputable def collisionBeta (M R : ℕ) : ℝ :=
  2 * Real.sqrt ((R : ℝ) / M * (1 - (R : ℝ) / M))

/-- `0 ≤ β ≤ 1`, since `ρ (1 - ρ) ≤ 1/4` for every real `ρ`.

Proof sketch: `Real.sqrt_nonneg`; and `ρ (1 - ρ) ≤ 1/4` (`nlinarith [sq_nonneg (ρ - 1/2)]`)
gives `√(ρ (1 - ρ)) ≤ √(1/4) = 1/2` (`Real.sqrt_le_sqrt`, `Real.sqrt_eq_iff`).
Reference: tex 1593-1596; node L08.  [leaf: easy] -/
theorem collisionBeta_nonneg_le_one (M R : ℕ) :
    0 ≤ collisionBeta M R ∧ collisionBeta M R ≤ 1 := by
  unfold collisionBeta
  refine ⟨by positivity, ?_⟩
  have h1 : (R : ℝ) / M * (1 - (R : ℝ) / M) ≤ (1 / 2) ^ 2 := by
    nlinarith [sq_nonneg ((R : ℝ) / M - 1 / 2)]
  have h2 : Real.sqrt ((R : ℝ) / M * (1 - (R : ℝ) / M)) ≤ 1 / 2 :=
    (Real.sqrt_le_left (by norm_num)).2 h1
  linarith

/-- **Sphere intersections as a filter on flip sets.**  For `u, v` of length `M`, with
`D = diffSet M u v`, a string `z` lies in `S_u ∩ S_v` iff it has length `M`, its flip set
`F = diffSet M u z` has `|F| = R`, and `2 |F ∩ D| = |D|`.

Proof sketch: `ext z`; `mem_inter`, `mem_hammingSphere_iff_diffSet`; by `diffSet_symmDiff`,
`diffSet M v z = D Δ F` and `|D Δ F| + 2 |D ∩ F| = |D| + |F|`
(`card_sdiff_add_card_inter`, `symmDiff_def`, `card_union_of_disjoint`), so with `|F| = R` the
condition `|D Δ F| = R` is `2 |F ∩ D| = |D|` (`inter_comm`, `omega`).
Reference: tex 1290-1295; node L08.  [leaf: medium] -/
theorem sphere_inter_eq_filter_diffSet (M R : ℕ) (u v : BitString) (hu : u.length = M)
    (hv : v.length = M) :
    hammingSphere M u R ∩ hammingSphere M v R =
      (stringsOfLength M).filter (fun z => (diffSet M u z).card = R ∧
        2 * (diffSet M u z ∩ diffSet M u v).card = (diffSet M u v).card) := by
  have key : ∀ D F : Finset ℕ, (symmDiff D F).card + 2 * (F ∩ D).card = D.card + F.card := by
    intro D F
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have h1 := Finset.card_sdiff_add_card_inter D F
    have h2 := Finset.card_sdiff_add_card_inter F D
    rw [Finset.inter_comm D F] at h1
    omega
  ext z
  rw [Finset.mem_inter, mem_hammingSphere_iff_diffSet hu, mem_hammingSphere_iff_diffSet hv,
    Finset.mem_filter, mem_stringsOfLength, diffSet_symmDiff M u v z]
  have hk := key (diffSet M u v) (diffSet M u z)
  constructor
  · rintro ⟨⟨hz, hF⟩, -, hDF⟩
    exact ⟨hz, hF, by omega⟩
  · rintro ⟨hz, hF, h2⟩
    exact ⟨⟨hz, hF⟩, hz, by omega⟩

/-- Filtering the powerset by cardinality is `powersetCard`.

Proof sketch: `Finset.powersetCard_eq_filter` and `Finset.filter_filter`.
Reference: tex 1290-1295; node L08.  [leaf: easy] -/
theorem powerset_filter_card_eq (M R : ℕ) (D : Finset ℕ) :
    (range M).powerset.filter (fun F => F.card = R ∧ 2 * (F ∩ D).card = D.card) =
      ((range M).powersetCard R).filter (fun F => 2 * (F ∩ D).card = D.card) := by
  rw [Finset.powersetCard_eq_filter, Finset.filter_filter]

/-- **Sphere intersections as flip sets.**  For `u, v` of length `M`, with
`D = diffSet M u v` (so `|D| = dist(u, v)`), the common points of `S_u` and `S_v` correspond to
the `R`-subsets `F ⊆ range M` with `2 |F ∩ D| = |D|`; in particular the intersection is empty
for odd distance. -/
theorem card_sphere_inter_eq (M R : ℕ) (u v : BitString) (hu : u.length = M)
    (hv : v.length = M) :
    (hammingSphere M u R ∩ hammingSphere M v R).card =
      (((range M).powersetCard R).filter
        (fun F => 2 * (F ∩ diffSet M u v).card = (diffSet M u v).card)).card := by
  rw [sphere_inter_eq_filter_diffSet M R u v hu hv, ← powerset_filter_card_eq M R]
  exact card_filter_diffSet M u hu
    (fun F => F.card = R ∧ 2 * (F ∩ diffSet M u v).card = (diffSet M u v).card)

/-- **Markov's inequality for the balanced event.**  For `a ≥ 0`, every `F` with
`2 |F ∩ D| = |D|` contributes `a^|F ∩ D| = (√a)^|D|`, all other terms are nonnegative.

Proof sketch: `sum_le_sum_of_subset_of_nonneg` (filter ⊆ P), then on the filter rewrite
`a = √a ^ 2` (`Real.sq_sqrt`), `pow_mul`, and `sum_const`, `nsmul_eq_mul`.
Reference: tex 1307-1311 (Markov with `a = (1-ρ)/ρ`); node L08.  [leaf: easy] -/
theorem card_filter_mul_sqrt_pow_le (P : Finset (Finset ℕ)) (D : Finset ℕ) {a : ℝ}
    (ha : 0 ≤ a) :
    ((P.filter (fun F => 2 * (F ∩ D).card = D.card)).card : ℝ) * Real.sqrt a ^ D.card ≤
      ∑ F ∈ P, a ^ (F ∩ D).card := by
  have hterm : ∀ F ∈ P.filter (fun F => 2 * (F ∩ D).card = D.card),
      Real.sqrt a ^ D.card = a ^ (F ∩ D).card := by
    intro F hF
    rw [← (Finset.mem_filter.1 hF).2, pow_mul, Real.sq_sqrt ha]
  calc ((P.filter (fun F => 2 * (F ∩ D).card = D.card)).card : ℝ) * Real.sqrt a ^ D.card
      = ∑ F ∈ P.filter (fun F => 2 * (F ∩ D).card = D.card), Real.sqrt a ^ D.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ F ∈ P.filter (fun F => 2 * (F ∩ D).card = D.card), a ^ (F ∩ D).card :=
        Finset.sum_congr rfl hterm
    _ ≤ ∑ F ∈ P, a ^ (F ∩ D).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun F _ _ => pow_nonneg ha _

/-- **The collision base.**  With `ρ = R / M ∈ (0, 1)` and `a = (1 - ρ) / ρ`:
`1 - ρ + ρ a = β √a`.

Proof sketch: the left side is `2 (1 - ρ)`; `β √a = 2 √(ρ (1 - ρ) (1 - ρ) / ρ) = 2 (1 - ρ)`
(`Real.sqrt_mul_self`, `← Real.sqrt_mul`, `field_simp`).
Reference: tex 1309-1311; node L08.  [leaf: easy] -/
theorem collision_base_eq {M R : ℕ} (hR : 0 < R) (hRM : R < M) :
    1 - (R : ℝ) / M + (R : ℝ) / M * ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) =
      collisionBeta M R * Real.sqrt ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast hR.trans hRM
  have hρ0 : (0 : ℝ) < (R : ℝ) / M := div_pos (by exact_mod_cast hR) hM
  have hρ1 : (R : ℝ) / M < 1 := (div_lt_one hM).2 (by exact_mod_cast hRM)
  have hprod : (R : ℝ) / M * (1 - (R : ℝ) / M) * ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) =
      (1 - (R : ℝ) / M) ^ 2 := by
    field_simp
  unfold collisionBeta
  rw [mul_assoc, ← Real.sqrt_mul (mul_nonneg hρ0.le (sub_nonneg.2 hρ1.le)), hprod,
    Real.sqrt_sq (sub_nonneg.2 hρ1.le)]
  field_simp
  ring

/-- **Exact-sphere collisions** (blueprint node L08, first claim of `lem:ham-collision`).  For
`u, v` of length `M`, `0 < R` and `2 R ≤ M`:
`|S_u ∩ S_v| / (M choose R) ≤ β^dist(u, v)`, `β = 2 √(ρ (1 - ρ))`, `ρ = R / M`. -/
theorem sphereCollisionBound (M R : ℕ) (u v : BitString) (hu : u.length = M)
    (hv : v.length = M) (hR : 0 < R) (hRM : 2 * R ≤ M) :
    ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) / M.choose R ≤
      collisionBeta M R ^ hammingDist u v := by
  have hRM' : R < M := by omega
  have hM : 0 < M := by omega
  have hρ0 : (0 : ℝ) < (R : ℝ) / M := div_pos (Nat.cast_pos.mpr hR) (Nat.cast_pos.mpr hM)
  have hρ1 : (R : ℝ) / M < 1 := (div_lt_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_lt.mpr hRM')
  have ha0 : 0 < (1 - (R : ℝ) / M) / ((R : ℝ) / M) := div_pos (sub_pos.mpr hρ1) hρ0
  have hsa : 0 < Real.sqrt ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) := Real.sqrt_pos.mpr ha0
  have hD : diffSet M u v ⊆ range M := filter_subset _ _
  have hmgf := hypergeometricMGF_dual (range M) (diffSet M u v) hD R
    (by rw [card_range]; exact hRM'.le) (by rw [card_range]; exact hM) ha0.le
  rw [card_range] at hmgf
  have hmarkov := card_filter_mul_sqrt_pow_le ((range M).powersetCard R) (diffSet M u v) ha0.le
  rw [← card_sphere_inter_eq M R u v hu hv] at hmarkov
  have hNpos : (0 : ℝ) < M.choose R := by exact_mod_cast Nat.choose_pos hRM'.le
  rw [div_le_iff₀ hNpos, hammingDist_eq_card_diffSet hu hv]
  refine le_of_mul_le_mul_right ?_ (pow_pos hsa (diffSet M u v).card)
  calc ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) *
        Real.sqrt ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) ^ (diffSet M u v).card
      ≤ ∑ F ∈ (range M).powersetCard R,
          ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) ^ (F ∩ diffSet M u v).card := hmarkov
    _ ≤ (M.choose R : ℝ) * (1 - (R : ℝ) / M + (R : ℝ) / M *
          ((1 - (R : ℝ) / M) / ((R : ℝ) / M))) ^ (diffSet M u v).card := hmgf
    _ = collisionBeta M R ^ (diffSet M u v).card * M.choose R *
          Real.sqrt ((1 - (R : ℝ) / M) / ((R : ℝ) / M)) ^ (diffSet M u v).card := by
      rw [collision_base_eq hR hRM', mul_pow]
      ring

/-! ### L09: the heavy-cell bound -/

/-- The heavy pairs `(z, u)` of the experiment of `eq:ham-heavy-bound`: `z` in the cube,
`u ∈ S_z`, the cell `Q u` of `u` has at least `2^ℓ` points and `|Q u ∩ S_z| > 2^-δ |Q u|`. -/
def heavyPairs (M R ℓ δ : ℕ) (Q : BitString → Finset BitString) :
    Finset (BitString × BitString) :=
  ((stringsOfLength M) ×ˢ (stringsOfLength M)).filter (fun p =>
    p.2 ∈ hammingSphere M p.1 R ∧ 2 ^ ℓ ≤ (Q p.2).card ∧
      (Q p.2).card < 2 ^ δ * (Q p.2 ∩ hammingSphere M p.1 R).card)

/-- The heavy fibre of a point `u`: the centers `z ∈ S_u` making `(z, u)` heavy. -/
def heavyFiber (M R ℓ δ : ℕ) (Q : BitString → Finset BitString) (u : BitString) :
    Finset BitString :=
  (hammingSphere M u R).filter (fun z =>
    2 ^ ℓ ≤ (Q u).card ∧ (Q u).card < 2 ^ δ * (Q u ∩ hammingSphere M z R).card)

/-- **Sampling symmetry.**  Uniform `z` then uniform `u ∈ S_z` is the same experiment as
uniform `u` then uniform `z ∈ S_u`: the heavy pairs are counted fibre by fibre over `u`.

Proof sketch: `card_eq_sum_card_fiberwise` on `p ↦ p.2`, then for `u` in the cube the fibre is
the image of `heavyFiber … u` under `z ↦ (z, u)`; use `mem_hammingSphere_comm` (both strings
have length `M`) and `mem_stringsOfLength`.
Reference: tex 1327-1332; node L09.  [leaf: medium] -/
theorem card_heavyPairs_eq_sum (M R ℓ δ : ℕ) (Q : BitString → Finset BitString) :
    (heavyPairs M R ℓ δ Q).card = ∑ u ∈ stringsOfLength M, (heavyFiber M R ℓ δ Q u).card := by
  have hmaps : ∀ p ∈ heavyPairs M R ℓ δ Q, p.2 ∈ stringsOfLength M := fun p hp =>
    (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := heavyPairs M R ℓ δ Q)
    (t := stringsOfLength M) fun p hp => hmaps p hp]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := (mem_stringsOfLength M u).1 hu
  have hmem : ∀ z, (z, u) ∈ heavyPairs M R ℓ δ Q ↔ z ∈ heavyFiber M R ℓ δ Q u := by
    intro z
    simp only [heavyPairs, heavyFiber, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hz, -⟩, hs, hl, hd⟩
      exact ⟨(mem_hammingSphere_comm hu' ((mem_stringsOfLength M z).1 hz)).1 hs, hl, hd⟩
    · rintro ⟨hs, hl, hd⟩
      have hz := ((mem_hammingSphere_iff_diffSet hu').1 hs).1
      exact ⟨⟨(mem_stringsOfLength M z).2 hz, hu⟩, (mem_hammingSphere_comm hu' hz).2 hs, hl, hd⟩
  refine Finset.card_nbij' Prod.fst (fun z => (z, u)) ?_ ?_ ?_ ?_
  · rintro ⟨z, w⟩ hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hp, rfl⟩ := hp
    exact (hmem z).1 hp
  · intro z hz
    rw [Finset.mem_coe] at hz
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨(hmem z).2 hz, rfl⟩
  · rintro ⟨z, w⟩ hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨-, rfl⟩ := hp
    rfl
  · intro z _
    rfl

/-- **Markov's inequality on one fibre.**  Every `z` in the heavy fibre of `u` has
`|Q u| ≤ 2^δ |Q u ∩ S_z|`.

Proof sketch: `card_nsmul_le_sum`-style bound over the filter, then
`sum_le_sum_of_subset_of_nonneg` (filter ⊆ `S_u`).
Reference: tex 1324-1326; node L09.  [leaf: easy] -/
theorem heavyFiber_card_mul_le (M R ℓ δ : ℕ) (Q : BitString → Finset BitString)
    (u : BitString) :
    (heavyFiber M R ℓ δ Q u).card * (Q u).card ≤
      2 ^ δ * ∑ z ∈ hammingSphere M u R, (Q u ∩ hammingSphere M z R).card := by
  have hsub : heavyFiber M R ℓ δ Q u ⊆ hammingSphere M u R := Finset.filter_subset _ _
  calc (heavyFiber M R ℓ δ Q u).card * (Q u).card
      = ∑ _z ∈ heavyFiber M R ℓ δ Q u, (Q u).card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ z ∈ heavyFiber M R ℓ δ Q u, 2 ^ δ * (Q u ∩ hammingSphere M z R).card :=
        Finset.sum_le_sum fun _z hz => (Finset.mem_filter.1 hz).2.2.le
    _ = 2 ^ δ * ∑ z ∈ heavyFiber M R ℓ δ Q u, (Q u ∩ hammingSphere M z R).card := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ δ * ∑ z ∈ hammingSphere M u R, (Q u ∩ hammingSphere M z R).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hsub)

/-- **Double counting.**  For a cell `Q` inside the cube and `u` of length `M`,
`∑_{z ∈ S_u} |Q ∩ S_z| = ∑_{v ∈ Q} |S_u ∩ S_v|`.

Proof sketch: both sides count pairs `(z, v)` with `z ∈ S_u`, `v ∈ Q`, `v ∈ S_z`
(`card_eq_sum_ones`, `sum_comm`, `sum_filter`), and `v ∈ S_z ↔ z ∈ S_v` by
`mem_hammingSphere_comm` (`Q ⊆ stringsOfLength M`, `S_u ⊆ stringsOfLength M`).
Reference: tex 1318-1321; node L09.  [leaf: medium] -/
theorem sum_card_inter_sphere_eq (M R : ℕ) (Q : Finset BitString)
    (hQ : Q ⊆ stringsOfLength M) (u : BitString) (hu : u.length = M) :
    ∑ z ∈ hammingSphere M u R, (Q ∩ hammingSphere M z R).card =
      ∑ v ∈ Q, (hammingSphere M u R ∩ hammingSphere M v R).card := by
  simp only [← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun z hz => ?_
  have hvl := (mem_stringsOfLength M v).1 (hQ hv)
  have hzl := ((mem_hammingSphere_iff_diffSet hu).1 hz).1
  simp only [mem_hammingSphere_comm hvl hzl]

/-- **Near points of a cell.**  For `Q` inside the cube and `u` of length `M`, at most
`V(M, h - 1)` points of `Q` lie within distance `h - 1` of `u`.

Proof sketch: the filter is contained in `hammingBall M u (h - 1)` (`hammingBall`,
`mem_filter`, `hQ`, `hammingDist_comm` if needed), whose size is `hammingVol M (h - 1)`
(`hammingBall_card`); `card_le_card`.
Reference: tex 1321-1323 ("at most `V(M, h-1)` nearby `v`"); node L09.  [leaf: easy] -/
theorem card_filter_dist_le (M h : ℕ) (Q : Finset BitString) (hQ : Q ⊆ stringsOfLength M)
    (u : BitString) (hu : u.length = M) :
    (Q.filter (fun v => hammingDist u v ≤ h - 1)).card ≤ hammingVol M (h - 1) := by
  rw [← hammingBall_card M u (h - 1) hu]
  refine Finset.card_le_card fun v hv => ?_
  rw [Finset.mem_filter] at hv
  rw [hammingBall, Finset.mem_filter]
  exact ⟨hQ hv.1, hv.2⟩

/-- **A collision count is at most the sphere size**: `|S_u ∩ S_v| ≤ (M choose R)`.

Proof sketch: `card_le_card inter_subset_left` and `hammingSphere_card`.
Reference: tex 1321-1323; node L09.  [leaf: easy] -/
theorem card_sphere_inter_le_choose (M R : ℕ) (u v : BitString) (hu : u.length = M) :
    (hammingSphere M u R ∩ hammingSphere M v R).card ≤ M.choose R := by
  rw [← hammingSphere_card M u R hu]
  exact Finset.card_le_card Finset.inter_subset_left

/-- **Far pairs**: if `dist(u, v) ≥ h` then `|S_u ∩ S_v| ≤ N β^h` (from `sphereCollisionBound`
and `0 ≤ β ≤ 1`). -/
theorem card_sphere_inter_le_far (M R h : ℕ) (hR : 0 < R) (hRM : 2 * R ≤ M) (u v : BitString)
    (hu : u.length = M) (hv : v.length = M) (hd : h ≤ hammingDist u v) :
    ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) ≤
      M.choose R * collisionBeta M R ^ h := by
  have hN : (0 : ℝ) < M.choose R := by exact_mod_cast Nat.choose_pos (by omega : R ≤ M)
  have h1 := sphereCollisionBound M R u v hu hv hR hRM
  rw [div_le_iff₀ hN] at h1
  obtain ⟨hβ0, hβ1⟩ := collisionBeta_nonneg_le_one M R
  calc ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ)
      ≤ collisionBeta M R ^ hammingDist u v * M.choose R := h1
    _ ≤ collisionBeta M R ^ h * M.choose R :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hβ0 hβ1 hd) hN.le
    _ = M.choose R * collisionBeta M R ^ h := mul_comm _ _

/-- **Near pairs and far pairs.**  For a cell `Q` inside the cube, `u` of length `M`, `h ≥ 1`,
`0 < R`, `2 R ≤ M`: `∑_{v ∈ Q} |S_u ∩ S_v| ≤ N (V(M, h-1) + |Q| β^h)`, `N = (M choose R)`.
Near `v` (distance `≤ h - 1`) are at most `V(M, h - 1)` and contribute at most `N` each; far
`v` contribute at most `N β^h` each. -/
theorem sum_card_sphere_inter_le (M R h : ℕ) (hR : 0 < R) (hRM : 2 * R ≤ M) (hh : 1 ≤ h)
    (Q : Finset BitString) (hQ : Q ⊆ stringsOfLength M) (u : BitString) (hu : u.length = M) :
    (∑ v ∈ Q, ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ)) ≤
      M.choose R * (hammingVol M (h - 1) + Q.card * collisionBeta M R ^ h) := by
  have hN0 : (0 : ℝ) ≤ M.choose R := Nat.cast_nonneg _
  have hβ := (collisionBeta_nonneg_le_one M R).1
  have hnear : ∑ v ∈ Q.filter (fun v => hammingDist u v ≤ h - 1),
      ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) ≤
        M.choose R * hammingVol M (h - 1) := by
    calc ∑ v ∈ Q.filter (fun v => hammingDist u v ≤ h - 1),
          ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ)
        ≤ ∑ _v ∈ Q.filter (fun v => hammingDist u v ≤ h - 1), (M.choose R : ℝ) :=
          Finset.sum_le_sum fun v _ => by
            exact_mod_cast card_sphere_inter_le_choose M R u v hu
      _ = (Q.filter (fun v => hammingDist u v ≤ h - 1)).card * (M.choose R : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ hammingVol M (h - 1) * (M.choose R : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_dist_le M h Q hQ u hu) hN0
      _ = M.choose R * hammingVol M (h - 1) := mul_comm _ _
  have hfar : ∑ v ∈ Q.filter (fun v => ¬ hammingDist u v ≤ h - 1),
      ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) ≤
        Q.card * (M.choose R * collisionBeta M R ^ h) := by
    calc ∑ v ∈ Q.filter (fun v => ¬ hammingDist u v ≤ h - 1),
          ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ)
        ≤ ∑ _v ∈ Q.filter (fun v => ¬ hammingDist u v ≤ h - 1),
            (M.choose R * collisionBeta M R ^ h : ℝ) :=
          Finset.sum_le_sum fun v hv => card_sphere_inter_le_far M R h hR hRM u v hu
            ((mem_stringsOfLength M v).1 (hQ (Finset.mem_filter.1 hv).1))
            (by have := (Finset.mem_filter.1 hv).2; omega)
      _ = (Q.filter (fun v => ¬ hammingDist u v ≤ h - 1)).card *
            (M.choose R * collisionBeta M R ^ h : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q.card * (M.choose R * collisionBeta M R ^ h : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _)
            (mul_nonneg hN0 (pow_nonneg hβ _))
  calc (∑ v ∈ Q, ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ))
      = ∑ v ∈ Q.filter (fun v => hammingDist u v ≤ h - 1),
          ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) +
        ∑ v ∈ Q.filter (fun v => ¬ hammingDist u v ≤ h - 1),
          ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) :=
        (Finset.sum_filter_add_sum_filter_not Q _ _).symm
    _ ≤ M.choose R * hammingVol M (h - 1) + Q.card * (M.choose R * collisionBeta M R ^ h) :=
        add_le_add hnear hfar
    _ = M.choose R * (hammingVol M (h - 1) + Q.card * collisionBeta M R ^ h) := by ring

/-- **The heavy fibre of one point.**  For `u` of length `M`, the number of centers `z ∈ S_u`
making `(z, u)` heavy is at most `N 2^δ (V(M, h-1) 2^-ℓ + β^h)`. -/
theorem heavyFiber_card_le (M R ℓ δ h : ℕ) (hR : 0 < R) (hRM : 2 * R ≤ M) (hh : 1 ≤ h)
    (Q : BitString → Finset BitString) (hQ : ∀ u, Q u ⊆ stringsOfLength M) (u : BitString)
    (hu : u.length = M) :
    ((heavyFiber M R ℓ δ Q u).card : ℝ) ≤
      M.choose R * (2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h)) := by
  have hβ := (collisionBeta_nonneg_le_one M R).1
  by_cases hL : 2 ^ ℓ ≤ (Q u).card
  · have hL' : (2 : ℝ) ^ ℓ ≤ (Q u).card := by exact_mod_cast hL
    have hLpos : (0 : ℝ) < (Q u).card := lt_of_lt_of_le (by positivity) hL'
    have hLne : ((Q u).card : ℝ) ≠ 0 := hLpos.ne'
    have h1 : ((heavyFiber M R ℓ δ Q u).card : ℝ) * (Q u).card ≤
        2 ^ δ * ∑ v ∈ Q u, ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) := by
      have := heavyFiber_card_mul_le M R ℓ δ Q u
      rw [sum_card_inter_sphere_eq M R (Q u) (hQ u) u hu] at this
      exact_mod_cast this
    have h2 := sum_card_sphere_inter_le M R h hR hRM hh (Q u) (hQ u) u hu
    have h3 : ((heavyFiber M R ℓ δ Q u).card : ℝ) * (Q u).card ≤
        (M.choose R * (2 ^ δ * (hammingVol M (h - 1) / (Q u).card + collisionBeta M R ^ h))) *
          (Q u).card := by
      calc ((heavyFiber M R ℓ δ Q u).card : ℝ) * (Q u).card
          ≤ 2 ^ δ * ∑ v ∈ Q u, ((hammingSphere M u R ∩ hammingSphere M v R).card : ℝ) := h1
        _ ≤ 2 ^ δ * (M.choose R * (hammingVol M (h - 1) + (Q u).card * collisionBeta M R ^ h)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by field_simp
    calc ((heavyFiber M R ℓ δ Q u).card : ℝ)
        ≤ M.choose R * (2 ^ δ * (hammingVol M (h - 1) / (Q u).card + collisionBeta M R ^ h)) :=
          le_of_mul_le_mul_right h3 hLpos
      _ ≤ M.choose R * (2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hL') le_rfl
  · have hempty : heavyFiber M R ℓ δ Q u = ∅ :=
      Finset.filter_false_of_mem fun z _ hz => hL hz.1
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by positivity) (add_nonneg (by positivity) (pow_nonneg hβ _)))

/-- **Heavy-cell bound for an arbitrary cell assignment** (blueprint node L09, the general
form).  For `0 < R`, `2 R ≤ M`, `h ≥ 1`, natural `ℓ, δ`, and any `Q` assigning to each point a
set of points of the cube: with `Z` uniform on the cube and `U` uniform on `S_Z`,
`Pr[|Q U| ≥ 2^ℓ ∧ |Q U ∩ S_Z| > 2^-δ |Q U|] ≤ 2^δ (V(M, h-1) 2^-ℓ + β^h)`.
The probability is the number of heavy pairs over the `2^M (M choose R)` pairs `(z, u ∈ S_z)`. -/
theorem partitionHeavyBound_of_cells (M R ℓ δ h : ℕ) (hR : 0 < R) (hRM : 2 * R ≤ M)
    (hh : 1 ≤ h) (Q : BitString → Finset BitString) (hQ : ∀ u, Q u ⊆ stringsOfLength M) :
    ((heavyPairs M R ℓ δ Q).card : ℝ) / (2 ^ M * M.choose R) ≤
      2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h) := by
  have hNpos : (0 : ℝ) < M.choose R := by exact_mod_cast Nat.choose_pos (by omega : R ≤ M)
  rw [div_le_iff₀ (mul_pos (by positivity) hNpos), card_heavyPairs_eq_sum, Nat.cast_sum]
  calc ∑ u ∈ stringsOfLength M, ((heavyFiber M R ℓ δ Q u).card : ℝ)
      ≤ ∑ _u ∈ stringsOfLength M, (M.choose R : ℝ) *
          (2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h)) :=
        Finset.sum_le_sum fun u hu =>
          heavyFiber_card_le M R ℓ δ h hR hRM hh Q hQ u ((mem_stringsOfLength M u).1 hu)
    _ = _ := by
      rw [Finset.sum_const, card_stringsOfLength, nsmul_eq_mul]
      push_cast
      ring

/-- The parts of a finite partition of the cube lie in the cube.

Proof sketch: if `u ∈ stringsOfLength M`, `P.part u ∈ P.parts` (`Finpartition.part_mem`) and
parts are subsets (`P.le`); otherwise `P.part u = ∅` (`Finpartition.part_eq_empty`).
Reference: tex 4500-4503 (exact partitions); node L09.  [leaf: easy] -/
theorem finpartition_part_subset {M : ℕ} (P : Finpartition (stringsOfLength M)) (u : BitString) :
    P.part u ⊆ stringsOfLength M := by
  exact P.part_subset u

/-- **Heavy-cell bound** (blueprint node L09, `eq:ham-heavy-bound`).  For a finite partition `P`
of the cube `{0,1}^M`, `0 < R`, `2 R ≤ M`, `h ≥ 1` and natural `ℓ, δ`: if `Z` is uniform on the
cube and `U` uniform on `S_Z`, then
`Pr[|P(U)| ≥ 2^ℓ ∧ |P(U) ∩ S_Z| > 2^-δ |P(U)|] ≤ 2^δ (V(M, h-1) 2^-ℓ + β^h)`. -/
theorem partitionHeavyBound (M R ℓ δ h : ℕ) (hR : 0 < R) (hRM : 2 * R ≤ M) (hh : 1 ≤ h)
    (P : Finpartition (stringsOfLength M)) :
    ((heavyPairs M R ℓ δ (fun u => P.part u)).card : ℝ) / (2 ^ M * M.choose R) ≤
      2 ^ δ * (hammingVol M (h - 1) / 2 ^ ℓ + collisionBeta M R ^ h) :=
  partitionHeavyBound_of_cells M R ℓ δ h hR hRM hh _ (finpartition_part_subset P)

end Kolmogorov.StrongMerging.Lower
