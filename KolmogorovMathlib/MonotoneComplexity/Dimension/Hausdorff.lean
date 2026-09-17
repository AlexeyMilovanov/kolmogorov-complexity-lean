/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.Dimension.LowComplexityCover
import KolmogorovMathlib.Core.Basic
import Mathlib.Order.LiminfLimsup

/-!
# Effective Hausdorff dimension: the complexity characterizations (SUV §5.8)

Theorem 119 reduces the dimension of a set to the dimensions of its singletons,
and Theorem 120 identifies the dimension of a singleton with the lower limit of
the normalized plain Kolmogorov complexity of its prefixes.

## Rendering decisions

* Theorem 119 uses `sSup` of the image of `A` under `ω ↦ dim {ω}`.  The empty
  set is included: both sides are `0` there (`Real.sSup_empty = 0`, and `∅` is
  an effective `α`-null set for every `α > 0`), so no nonemptiness hypothesis is
  added, matching the source, which states no such hypothesis.
* Theorem 120 uses Mathlib's `Filter.liminf … Filter.atTop` on `ℝ` rather than
  an explicit `ε`-`N` form.  Reason: the sequence `n ↦ C((ω)_n)/n` is bounded
  (`0 ≤ · ≤ 1 + O(1/n)` by `C(x) ≤ l(x) + O(1)`), so `ℝ`'s conditionally
  complete `liminf` is the classical lower limit with no junk value, and the
  statement then reads exactly like the displayed formula of p. 174.  The
  `n = 0` term is `0` (division by zero) and is irrelevant at `atTop`.
* The complexity is *plain* complexity `C` of the prefixes, as displayed in the
  source; `V` is an optimal (universal) decompressor, following the repository
  convention `(V : Map) (hV : isOptimalConditional V)` and the `ENat.toNat`
  cast used by Theorems 86 and 99.  The source's parenthetical remark that other
  complexity versions give the same limit is not asserted here.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## Monotonicity of the dimension and the dimension of `∅` -/

/-- The effective Hausdorff dimension is monotone in the set: an effective
`α`-null cover of `B` covers every subset of `B` (SUV §5.8, p. 173, "the property
is monotone … if `A` decreases"). -/
lemma effectiveHausdorffDim_mono {A B : Set CantorSeq} (h : A ⊆ B) :
    effectiveHausdorffDim A ≤ effectiveHausdorffDim B :=
  csInf_le_csInf (bddBelow_effectiveAlphaSet A) (nonempty_effectiveAlphaSet B)
    (fun _ hβ => ⟨hβ.1, hβ.2.mono_set h⟩)

/-- The empty set is an effective `α`-null set for every `α`: the empty cover
works. -/
lemma isEffectiveAlphaNull_empty (α : ℝ) : IsEffectiveAlphaNull α (∅ : Set CantorSeq) := by
  refine ⟨fun _ _ => none, (Computable.const none).to₂, fun ε hε => ⟨Set.empty_subset _, ?_⟩⟩
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  simp only [coverAlphaMass_none, tsum_zero]
  exact ENNReal.ofReal_pos.2 hε'

/-- The empty set has effective Hausdorff dimension zero. -/
@[simp] lemma effectiveHausdorffDim_empty : effectiveHausdorffDim (∅ : Set CantorSeq) = 0 := by
  refine le_antisymm ?_ (le_csInf (nonempty_effectiveAlphaSet _) fun b hb => hb.1.le)
  by_contra hcon
  simp only [not_le] at hcon
  have hmem : effectiveHausdorffDim (∅ : Set CantorSeq) / 2 ∈
      {α : ℝ | 0 < α ∧ IsEffectiveAlphaNull α (∅ : Set CantorSeq)} :=
    ⟨by linarith, isEffectiveAlphaNull_empty _⟩
  have hle := csInf_le (bddBelow_effectiveAlphaSet (∅ : Set CantorSeq)) hmem
  change effectiveHausdorffDim (∅ : Set CantorSeq) ≤ _ at hle
  linarith

/-- **SUV Theorem 119 (§5.8, p. 174).** The effective Hausdorff dimension of a
set is equal to the supremum of the effective Hausdorff dimensions of its
elements.

The proof is the source's: `≥` is monotonicity, and `≤` is "a direct corollary of
Theorem 117: all singletons are subsets of the largest effectively `r'`-null set,
so `A` is a subset of the same set and has dimension at most `r'`". -/
theorem effectiveHausdorffDim_eq_sSup_image (A : Set CantorSeq) :
    effectiveHausdorffDim A = sSup ((fun w => effectiveHausdorffDim {w}) '' A) := by
  rcases Set.eq_empty_or_nonempty A with rfl | hA
  · simp
  have hbdd : BddAbove ((fun w => effectiveHausdorffDim {w}) '' A) := by
    refine ⟨1, ?_⟩
    rintro y ⟨w, -, rfl⟩
    exact (effectiveHausdorffDim_mem_Icc {w}).2
  refine le_antisymm ?_ (csSup_le (hA.image _) ?_)
  · by_contra hcon
    simp only [not_le] at hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
    have h0 : (0 : ℝ) ≤ sSup ((fun w => effectiveHausdorffDim {w}) '' A) := by
      obtain ⟨w, hw⟩ := hA
      exact le_trans (effectiveHausdorffDim_mem_Icc {w}).1 (le_csSup hbdd ⟨w, hw, rfl⟩)
    have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt h0 hr1
    have hrQ : (0 : ℚ) < r := by exact_mod_cast hrpos
    obtain ⟨A', hA'null, hA'max⟩ := exists_largest_isEffectiveAlphaNull r hrQ
    have hsub : A ⊆ A' := by
      intro w hw
      refine hA'max {w} ?_ rfl
      exact isEffectiveAlphaNull_of_effectiveHausdorffDim_lt hrpos
        (lt_of_le_of_lt (le_csSup hbdd ⟨w, hw, rfl⟩) hr1)
    have hnull : IsEffectiveAlphaNull (r : ℝ) A := hA'null.mono_set hsub
    have hle : effectiveHausdorffDim A ≤ (r : ℝ) :=
      csInf_le (bddBelow_effectiveAlphaSet A) ⟨hrpos, hnull⟩
    linarith
  · rintro y ⟨w, hw, rfl⟩
    exact effectiveHausdorffDim_mono (Set.singleton_subset_iff.2 hw)

/-! ## Theorem 120: the two inequalities -/

/-- The normalized plain complexity of the prefixes of `ω` has its lower limit in
`[0,1]`. -/
theorem liminf_normalizedPlainK_mem_Icc (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) :
    Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
      Filter.atTop ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  set u : ℕ → ℝ := fun n => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) with hudef
  have hu0 : ∀ n, 0 ≤ u n := fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htoNat : ∀ n : ℕ, (plainK V (cantorPrefix w n)).toNat ≤ n + c := by
    intro n
    have h1 := hc (cantorPrefix w n)
    simp only [programLength, cantorPrefix_length] at h1
    have hrhs : ((n : ℕ∞) + (c : ℕ∞)) ≠ ⊤ :=
      WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top n, ENat.natCast_ne_top c⟩
    have h2 := ENat.toNat_le_toNat h1 hrhs
    rwa [ENat.toNat_add (ENat.natCast_ne_top n) (ENat.natCast_ne_top c), ENat.toNat_natCast,
      ENat.toNat_natCast] at h2
  have hub : ∀ n : ℕ, 1 ≤ n → u n ≤ 1 + (c : ℝ) / (n : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) + (c : ℝ) := by
      exact_mod_cast htoNat n
    calc u n = ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) := rfl
      _ ≤ ((n : ℝ) + (c : ℝ)) / (n : ℝ) := by gcongr
      _ = 1 + (c : ℝ) / (n : ℝ) := by field_simp
  have hM : ∀ᶠ n in Filter.atTop, u n ≤ 1 + (c : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 := hub n hn
    have h2 : (c : ℝ) / (n : ℝ) ≤ (c : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [(by positivity : (0 : ℝ) ≤ (c : ℝ))]
    linarith
  have hbddge : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨0, hu0⟩
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u := by
    refine ⟨1 + (c : ℝ), fun a ha => ?_⟩
    obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_map.1 ha).and hM).exists
    exact le_trans hn1 hn2
  constructor
  · rw [Filter.le_liminf_iff hcob hbddge]
    intro y hy
    filter_upwards with n
    exact lt_of_lt_of_le hy (hu0 n)
  · rw [Filter.liminf_le_iff hcob hbddge]
    intro y hy
    have hy1 : (0 : ℝ) < y - 1 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((c : ℝ) / (y - 1))
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hy1.le) hN
    have hcN : (c : ℝ) / (N : ℝ) < y - 1 :=
      (div_lt_iff₀ hNpos).2 (by nlinarith [(div_lt_iff₀ hy1).1 hN])
    refine Filter.Eventually.frequently ?_
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hn
    have h1 := hub n hn1
    have h2 : (c : ℝ) / (n : ℝ) ≤ (c : ℝ) / (N : ℝ) := by gcongr
    linarith

/-- The normalized plain complexity of the prefixes is cobounded from below
along `atTop`, which is what `Filter.frequently_lt_of_liminf_lt` needs: the
sequence is bounded above by `1 + c` where `C(x) ≤ l(x) + c`. -/
lemma isCoboundedUnder_normalizedPlainK (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) :
    Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ)) := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  set u : ℕ → ℝ := fun n => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) with hudef
  have htoNat : ∀ n : ℕ, (plainK V (cantorPrefix w n)).toNat ≤ n + c := by
    intro n
    have h1 := hc (cantorPrefix w n)
    simp only [programLength, cantorPrefix_length] at h1
    have hrhs : ((n : ℕ∞) + (c : ℕ∞)) ≠ ⊤ :=
      WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top n, ENat.natCast_ne_top c⟩
    have h2 := ENat.toNat_le_toNat h1 hrhs
    rwa [ENat.toNat_add (ENat.natCast_ne_top n) (ENat.natCast_ne_top c), ENat.toNat_natCast,
      ENat.toNat_natCast] at h2
  have hM : ∀ᶠ n in Filter.atTop, u n ≤ 1 + (c : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hcast : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (n : ℝ) + (c : ℝ) := by
      exact_mod_cast htoNat n
    have h1 : u n ≤ ((n : ℝ) + (c : ℝ)) / (n : ℝ) := by
      simp only [hudef]
      gcongr
    have h2 : ((n : ℝ) + (c : ℝ)) / (n : ℝ) = 1 + (c : ℝ) / (n : ℝ) := by field_simp
    have h3 : (c : ℝ) / (n : ℝ) ≤ (c : ℝ) := by
      rw [div_le_iff₀ hnpos]
      nlinarith [(by positivity : (0 : ℝ) ≤ (c : ℝ))]
    rw [h2] at h1
    linarith
  refine ⟨1 + (c : ℝ), fun a ha => ?_⟩
  obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_map.1 ha).and hM).exists
  exact le_trans hn1 hn2

/-- If the lower limit of `C((ω)_n)/n` is below the rational `r`, then
arbitrarily long prefixes of `ω` have plain complexity below `⌊r·n⌋`.  This is
the source's "the condition about lim inf guarantees that for infinitely many
`n` the `n`-bit prefix of `ω` is in the corresponding list" (p. 174). -/
lemma exists_low_prefix_of_liminf_lt (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) (r : ℚ) (hr : 0 < r)
    (h : Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
      Filter.atTop < (r : ℝ)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      plainK V (cantorPrefix w n) < ((alphaFloor r n : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn h
  have hgap : (0 : ℝ) < (r : ℝ) - (s : ℝ) := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((r : ℝ) - (s : ℝ)))
  have hKgap : (1 : ℝ) < ((r : ℝ) - (s : ℝ)) * (K : ℝ) := by
    have := mul_lt_mul_of_pos_left hK hgap
    rwa [mul_one_div, div_self (ne_of_gt hgap)] at this
  intro N
  have hfreq : ∃ᶠ n in Filter.atTop,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) < (s : ℝ) :=
    Filter.frequently_lt_of_liminf_lt (isCoboundedUnder_normalizedPlainK V hV w) hs1
  obtain ⟨n, hlt, hge⟩ :=
    (hfreq.and_eventually (Filter.eventually_ge_atTop (max N (max K 1)))).exists
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right K 1) (le_max_right N _)) hge
  have hnN : N ≤ n := le_trans (le_max_left N _) hge
  have hnK : (K : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_trans (le_max_left K 1) (le_max_right N _)) hge
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  refine ⟨n, hnN, ?_⟩
  have hnetop : plainK V (cantorPrefix w n) ≠ ⊤ := by
    intro hcon
    have h1 := hc (cantorPrefix w n)
    rw [hcon] at h1
    exact (WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top c⟩) (top_le_iff.1 h1)
  have hkey : ((plainK V (cantorPrefix w n)).toNat : ℝ) < ((alphaFloor r n : ℕ) : ℝ) := by
    have hA : ((plainK V (cantorPrefix w n)).toNat : ℝ) < (s : ℝ) * (n : ℝ) :=
      (div_lt_iff₀ hnpos).1 hlt
    have hB : (r : ℝ) * (n : ℝ) < ((alphaFloor r n : ℕ) : ℝ) + 1 :=
      (alphaFloor_spec r hr n).2
    have hC : (1 : ℝ) ≤ ((r : ℝ) - (s : ℝ)) * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hnK (le_of_lt hgap)
      linarith
    nlinarith
  have hnat : (plainK V (cantorPrefix w n)).toNat < alphaFloor r n := by exact_mod_cast hkey
  calc plainK V (cantorPrefix w n)
      = (((plainK V (cantorPrefix w n)).toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hnetop).symm
    _ < ((alphaFloor r n : ℕ) : ℕ∞) := by exact_mod_cast hnat

/-- **SUV Theorem 120, the upper bound (§5.8, pp. 174-175).**

> "Assume that the lim inf is less than a rational number `r`.  We have to verify
> that the set `{ω}` is an effectively `r'`-null set for each rational `r' > r`.
> For each `n` we consider all `n`-bit strings that have complexity less than
> `rn`.  There are at most `O(2^{rn})` such strings.  The condition about lim inf
> guarantees that for infinitely many `n` the `n`-bit prefix of `ω` is in the
> corresponding list. … there are `O(2^{rn})` terms and each is `2^{-r'n}`, so the
> sum is `O(2^{(r-r')n})`, and we get a converging geometric series."

The whole construction is carried out in `Dimension/LowComplexityCover.lean`
(`isEffectiveAlphaNull_singleton_of_forall_exists_low`); what remains here is the
translation of the `liminf` hypothesis into "arbitrarily long prefixes of `ω`
have complexity below `⌊r·n⌋`", which is `exists_low_prefix_of_liminf_lt`. -/
theorem isEffectiveAlphaNull_singleton_of_liminf_lt (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) (r r' : ℚ) (hr : 0 < r) (hrr' : r < r')
    (h : Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
      Filter.atTop < (r : ℝ)) :
    IsEffectiveAlphaNull ((r' : ℚ) : ℝ) {w} :=
  isEffectiveAlphaNull_singleton_of_forall_exists_low V hV.1 w r r' hr hrr'
    (exists_low_prefix_of_liminf_lt V hV w r hr h)

/-- **SUV Theorem 120, the lower bound (§5.8, p. 175).**

> "By definition, for each rational `ε > 0` we can generate a sequence of
> intervals. … Let us do this for `ε = 1, 1/2, 1/4, …`.  In this way we get a
> sequence of intervals that have finite sum of `r`th powers of their measures,
> and infinitely many of them cover `ω`. … The first statement implies that
> `m(i) ≥ c 2^{-r l(x_i)}` … `K(x_i) ≤ K(i) + O(1) ≤ r l(x_i) + O(1)` … the
> lengths of `x_i` tend to infinity … and the plain complexity does not exceed the
> prefix one."

Carried out here modulo the single leaf `exists_const_plainK_le_of_tsum_ne_top`
(`Dimension/LowComplexityCover.lean`), which is the source's
`K(x_i) ≤ K(i) + O(1) ≤ r·l(x_i) + O(1)` in plain-complexity form. -/
theorem liminf_le_of_isEffectiveAlphaNull_singleton (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) (r : ℚ) (hr : 0 < r) (h : IsEffectiveAlphaNull ((r : ℚ) : ℝ) {w}) :
    Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
      Filter.atTop ≤ (r : ℝ) := by
  classical
  obtain ⟨I, hIcomp, hI⟩ := h
  have hrR : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  set eps : ℕ → ℚ := fun j => (2 : ℚ)⁻¹ ^ (j + 1) with hepsdef
  have hepspos : ∀ j, 0 < eps j := fun j => by positivity
  set E : ℕ → Option BitString := fun m => I (eps (Nat.unpair m).1) (Nat.unpair m).2 with hEdef
  have hEcomp : Computable E := by
    have h1 : Computable (fun m : ℕ => eps (Nat.unpair m).1) :=
      computable_pow_half.comp
        ((Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)).to_comp)
    exact hIcomp.comp h1 ((Primrec.snd.comp Primrec.unpair).to_comp)
  -- each level weighs at most `2^{-(j+1)}`, so the whole family has finite weight
  have hlevel : ∀ j : ℕ,
      (∑' k, coverAlphaMass ((r : ℚ) : ℝ) (I (eps j) k)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
    intro j
    refine le_of_lt (lt_of_lt_of_le (hI (eps j) (hepspos j)).2 (le_of_eq ?_))
    rw [hepsdef, ofReal_pow_half_eq_dyadicValue, dyadicValue_one_eq_inv_two_pow']
  have hEsum : (∑' m, coverAlphaMass ((r : ℚ) : ℝ) (E m)) ≠ ⊤ := by
    have hsplit : (∑' m, coverAlphaMass ((r : ℚ) : ℝ) (E m))
        = ∑' j, ∑' k, coverAlphaMass ((r : ℚ) : ℝ) (I (eps j) k) := by
      rw [tsum_nat_pair]
      exact tsum_congr (fun j => tsum_congr (fun k => by simp [hEdef]))
    have hgeo : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1)) = 1 := by
      simpa using tsum_inv_two_pow_shift 0
    have hle : (∑' m, coverAlphaMass ((r : ℚ) : ℝ) (E m)) ≤ 1 := by
      rw [hsplit, ← hgeo]
      exact ENNReal.tsum_le_tsum hlevel
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  obtain ⟨c, hc⟩ := exists_const_plainK_le_of_tsum_ne_top V hV r hr E hEcomp hEsum
  -- arbitrarily long prefixes of `ω` are cheap
  have hrnum : ((r : ℚ) : ℝ) ≤ ((r.num.toNat : ℕ) : ℝ) := by
    have hden1 : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
    have hmul : ((r : ℚ) : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      rw [Rat.cast_def]; field_simp
    have hnn : (r.num : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
      have hpos : 0 ≤ r.num := le_of_lt (Rat.num_pos.2 hr)
      exact_mod_cast (Int.toNat_of_nonneg hpos).symm
    nlinarith
  have hkey : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      plainK V (cantorPrefix w n) ≤ ((alphaFloor r n + c : ℕ) : ℕ∞) := by
    intro N
    set j : ℕ := r.num.toNat * N with hjdef
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ((hI (eps j) (hepspos j)).1 rfl)
    cases hz : I (eps j) k with
    | none => rw [hz] at hk; simp at hk
    | some z =>
      rw [hz] at hk
      have hzpref : cantorPrefix w z.length = z :=
        (isCantorPrefix_iff_cantorPrefix_eq z w).1 hk
      have hmass : intervalAlphaMass ((r : ℚ) : ℝ) z < ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
        refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hI (eps j) (hepspos j)).2 (le_of_eq ?_))
        · calc intervalAlphaMass ((r : ℚ) : ℝ) z
              = coverAlphaMass ((r : ℚ) : ℝ) (I (eps j) k) := by rw [hz]; rfl
            _ ≤ ∑' i, coverAlphaMass ((r : ℚ) : ℝ) (I (eps j) i) := ENNReal.le_tsum k
        · rw [hepsdef, ofReal_pow_half_eq_dyadicValue, dyadicValue_one_eq_inv_two_pow']
      have hlen : ((j + 1 : ℕ) : ℝ) < (z.length : ℝ) * ((r : ℚ) : ℝ) :=
        lt_mul_length_of_intervalAlphaMass_lt hmass
      have hNlt : N ≤ z.length := by
        have hjR : ((r : ℚ) : ℝ) * (N : ℝ) ≤ (j : ℝ) := by
          rw [hjdef]
          push_cast
          exact mul_le_mul_of_nonneg_right hrnum (Nat.cast_nonneg N)
        have hlt : (N : ℝ) < (z.length : ℝ) := by
          have h1 : ((r : ℚ) : ℝ) * (N : ℝ) < (z.length : ℝ) * ((r : ℚ) : ℝ) := by
            push_cast at hlen
            linarith
          nlinarith
        exact le_of_lt (by exact_mod_cast hlt)
      refine ⟨z.length, hNlt, ?_⟩
      have hEeq : E (Nat.pair j k) = some z := by simp [hEdef, hz]
      have := hc (Nat.pair j k) z hEeq
      rwa [hzpref]
  -- the `liminf` estimate
  set u : ℕ → ℝ := fun n => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) with hudef
  have hu0 : ∀ n, 0 ≤ u n := fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.isBoundedUnder_of ⟨0, hu0⟩
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  refine Filter.liminf_le_of_frequently_le ?_ hbdd
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨P, hP⟩ := exists_nat_gt ((c : ℝ) / δ)
  obtain ⟨n, hn, hbound⟩ := hkey (max N₀ (max P 1))
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right P 1) (le_max_right N₀ _)) hn
  have hnP : (P : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_trans (le_max_left P 1) (le_max_right N₀ _)) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have htoNat : (plainK V (cantorPrefix w n)).toNat ≤ alphaFloor r n + c := by
    have hrhs : (((alphaFloor r n + c : ℕ) : ℕ∞)) ≠ ⊤ := ENat.natCast_ne_top _
    have h_eq : (((alphaFloor r n + c : ℕ) : ℕ∞)).toNat = alphaFloor r n + c :=
      ENat.toNat_natCast (alphaFloor r n + c)
    exact h_eq ▸ ENat.toNat_le_toNat hbound hrhs
  have hreal : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ ((r : ℚ) : ℝ) * (n : ℝ) + (c : ℝ) := by
    have h1 : ((plainK V (cantorPrefix w n)).toNat : ℝ)
        ≤ ((alphaFloor r n : ℕ) : ℝ) + (c : ℝ) := by exact_mod_cast htoNat
    have h2 : ((alphaFloor r n : ℕ) : ℝ) ≤ ((r : ℚ) : ℝ) * (n : ℝ) :=
      (alphaFloor_spec r hr n).1
    linarith
  have hPpos : (0 : ℝ) < (P : ℝ) :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg c) hδ.le) hP
  have hcδ : (c : ℝ) / (n : ℝ) ≤ δ := by
    have h1 : (c : ℝ) / (n : ℝ) ≤ (c : ℝ) / (P : ℝ) := by
      gcongr
    have h2 : (c : ℝ) / (P : ℝ) ≤ δ := by
      rw [div_le_iff₀ hPpos]
      have := (div_lt_iff₀ hδ).1 hP
      nlinarith
    linarith
  calc u n = ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ) := rfl
    _ ≤ (((r : ℚ) : ℝ) * (n : ℝ) + (c : ℝ)) / (n : ℝ) := by gcongr
    _ = ((r : ℚ) : ℝ) + (c : ℝ) / (n : ℝ) := by field_simp
    _ ≤ ((r : ℚ) : ℝ) + δ := by linarith

/-- **SUV Theorem 120 (§5.8, p. 174).** The effective Hausdorff dimension of a
singleton `{ω}`, where `ω = ω₀ω₁ω₂⋯`, equals

`liminf_{n→∞} C(ω₀ω₁⋯ω_{n-1}) / n`,

the lower limit of the plain Kolmogorov complexity of the `n`-bit prefixes of
`ω` divided by `n`. -/
theorem effectiveHausdorffDim_singleton_eq_liminf (V : Map) (hV : isOptimalConditional V)
    (w : CantorSeq) :
    effectiveHausdorffDim {w} =
      Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
        Filter.atTop := by
  set L := Filter.liminf (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) / (n : ℝ))
    Filter.atTop with hLdef
  have hL0 : 0 ≤ L := (liminf_normalizedPlainK_mem_Icc V hV w).1
  refine le_antisymm ?_ ?_
  · by_contra hcon
    simp only [not_le] at hcon
    obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hr'1
    have hrposR : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt hL0 hr1
    have hrpos : (0 : ℚ) < r := by exact_mod_cast hrposR
    have hrr' : r < r' := by exact_mod_cast hr2
    have hnull := isEffectiveAlphaNull_singleton_of_liminf_lt V hV w r r' hrpos hrr' hr1
    have hr'pos : (0 : ℝ) < (r' : ℝ) := lt_trans hrposR (by exact_mod_cast hrr')
    have hle : effectiveHausdorffDim {w} ≤ (r' : ℝ) :=
      csInf_le (bddBelow_effectiveAlphaSet {w}) ⟨hr'pos, hnull⟩
    linarith
  · refine le_csInf (nonempty_effectiveAlphaSet {w}) ?_
    rintro b ⟨hbpos, hbnull⟩
    by_contra hcon
    simp only [not_le] at hcon
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hcon
    have hrposR : (0 : ℝ) < (r : ℝ) := lt_trans hbpos hr1
    have hrpos : (0 : ℚ) < r := by exact_mod_cast hrposR
    have hnull : IsEffectiveAlphaNull ((r : ℚ) : ℝ) {w} := hbnull.mono_alpha hbpos hr1.le
    have hle := liminf_le_of_isEffectiveAlphaNull_singleton V hV w r hrpos hnull
    rw [← hLdef] at hle
    linarith

end Kolmogorov
