



/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint.GapCover
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayTestComputable
import KolmogorovMathlib.MonotoneComplexity.Omega.AntitoneSplit
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverInfra
import KolmogorovMathlib.MonotoneComplexity.Omega.BusyBeaverSearch
import KolmogorovMathlib.MonotoneComplexity.Omega.CappedScaling
import KolmogorovMathlib.MonotoneComplexity.Omega.IntervalCover
import KolmogorovMathlib.MonotoneComplexity.Omega.ModulusRandom
import KolmogorovMathlib.MonotoneComplexity.Omega.NeighbourhoodCover
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealCantor
import KolmogorovMathlib.MonotoneComplexity.Omega.NullRealKraft
import KolmogorovMathlib.MonotoneComplexity.Omega.OmegaBitsFromApprox
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionComputable
import KolmogorovMathlib.Prefix.UpperSemicomputableBound

/-!
# SUV Sections 5.7.5–5.7.7: slow convergence, Solovay functions, busy beavers

This module states the last three subsections of SUV Section 5.7 (pp. 165–172):

* the Solovay property of a computable series and Solovay functions (p. 165);
* **Theorem 111** (p. 165): the sum is random iff the series converges slowly in the
  Solovay sense;
* **Theorem 112** (p. 167): the grouping theorem for the Solovay property;
* **Theorem 113** (p. 168): tightness of an upper semicomputable bound for `K` iff
  `∑ 2^{-f(n)}` is random;
* the busy-beaver functions `BP`, `BP'`, `B` and convergence moduli (pp. 169–170);
* **Theorem 114** (p. 169), **Theorem 115** (p. 170), **Theorem 116** (p. 171).

## Definitional choices frozen here

* The Solovay property is stated *relative to a maximal lower semicomputable
  semimeasure `m` on `ℕ`*, exactly as the book does; every statement quantifies over
  such an `m`, so no particular choice is baked in.
* "`rᵢ/m(i) → 0`" is rendered by the book's own explication (p. 167): for every
  `ε > 0` the inequality `rᵢ ≥ ε·m(i)` holds for only finitely many `i`. This avoids
  choosing a topology on `ℝ≥0∞` quotients and is literally the source condition.
* `BP` is the maximal integer of prefix complexity at most `n` (p. 169); the a priori
  probability reformulations `BPapriori` and `BP'` (p. 170) are separate definitions,
  related to `BP` only by the explicitly stated `O(1)` bridges.
* **No cutoff is totalized.** Every "minimal `N` such that …" of pp. 169–170
  (`BPapriori`, `BPprime`, `convergenceModulus`) is `ℕ∞`-valued through `natSInfTop`,
  so an empty defining set gives `⊤` ("no such cutoff") instead of the junk `0` that
  raw `sInf : Set ℕ → ℕ` returns; `convergenceModulus` uses the source's own strict
  quantifier `n > N` (p. 169).  The maxima `BP`/`BPlain` keep `sSup`, but only
  together with the domain facts `kpNatSublevel_finite`/`kpNatSublevel_nonempty` and
  the characterisation `BP_mem_and_le` that makes them genuine maxima.
* Pair and rational codings go through the shared `natPairCode` / `ratBitCode` of
  `MonotoneComplexity/SharedCoding.lean` (`aprioriPair`, `aprioriRat`), not through ad
  hoc `Nat.pair` / `Encodable.encode` occurrences.
* `O(log n)` in Theorem 116 is rendered as `c * Nat.log 2 (n + 2) + c` with one
  constant `c` chosen before `n`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Slow convergence in the Solovay sense (SUV p. 165) -/

/-- The sequence of partial sums `a_n = r₀ + ⋯ + r_{n-1}` of a series of rationals. -/
def partialSums (r : ℕ → ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, r i

/-- The partial sums are the `ratRangeSum` of `Omega/LscBasic.lean`, hence computable. -/
theorem partialSums_eq_ratRangeSum (r : ℕ → ℚ) (n : ℕ) :
    partialSums r n = ratRangeSum r n := by
  induction n with
  | zero => simp [partialSums, ratRangeSum]
  | succ k ih =>
    rw [partialSums, Finset.sum_range_succ, ← partialSums, ih, ratRangeSum]

/-- The partial sums of a computable series of rationals are computable. -/
theorem computable_partialSums {r : ℕ → ℚ} (hr : Computable r) :
    Computable (partialSums r) :=
  (computable_ratRangeSum hr).of_eq fun n => (partialSums_eq_ratRangeSum r n).symm

/-- **SUV p. 165.** The computable series `∑ rᵢ` of nonnegative rationals *converges
slowly in the Solovay sense* (has the *Solovay property*) if the bound
`rᵢ = O(m(i))` is `O(1)`-tight infinitely often: `rᵢ ≥ ε·m(i)` for some `ε > 0` and
infinitely many `i`. -/
def HasSolovayProperty (m : ℕ → ℝ≥0∞) (r : ℕ → ℚ) : Prop :=
  ∃ ε : ℝ≥0∞, 0 < ε ∧ {i : ℕ | ε * m i ≤ ENNReal.ofReal ((r i : ℝ))}.Infinite

/-- **SUV p. 165.** "The series does not converge slowly if `rᵢ/m(i) → 0`", spelled
out as in the source (p. 167): for every `ε > 0` only finitely many `i` satisfy
`rᵢ ≥ ε·m(i)`. -/
def RatioTendstoZero (m : ℕ → ℝ≥0∞) (r : ℕ → ℚ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → {i : ℕ | ε * m i ≤ ENNReal.ofReal ((r i : ℝ))}.Finite

/-- Failure of the Solovay property is exactly `rᵢ/m(i) → 0`. -/
theorem not_hasSolovayProperty_iff (m : ℕ → ℝ≥0∞) (r : ℕ → ℚ) :
    ¬ HasSolovayProperty m r ↔ RatioTendstoZero m r := by
  simp only [HasSolovayProperty, RatioTendstoZero, not_exists, not_and, Set.not_infinite]

/-! #### Recalled Chapter-4 result (owner: `KolmogorovMathlib.Prefix.UpperSemicomputableBound`)

SUV Theorem 62 (p. 100) and the notion `IsUpperSemicomputableNat` it needs belong to
Chapter 4: Section 5.7 *uses* them and does not own them.  They are
declared once, in `KolmogorovMathlib/Prefix/UpperSemicomputableBound.lean`
(`IsUpperSemicomputableNat`, the two directions
`tsum_two_pow_neg_ne_top_of_KPPlain_le` / `KPPlain_le_of_tsum_two_pow_neg_ne_top` and
the assembled `KPPlain_le_iff_tsum_two_pow_neg_ne_top`), and Section 5.7 keeps only
the alias below.  `IsUpperSemicomputableNat` is used unchanged, straight from the owner
module. -/

/-- An upper semicomputable integer-valued `f` is an upper bound for `K(n)` up to an `O(1)`
additive term if and only if `∑ₙ 2^{-f(n)}` is finite. **Recalled Chapter-4 result, not a
C11 deliverable**: this is a one-line alias of the Chapter-4 owner
`KPPlain_le_iff_tsum_two_pow_neg_ne_top` (`Prefix/UpperSemicomputableBound.lean`),
instantiated at the canonical computable bijection `natToBitString` of `SharedCoding.lean`,
so that `K(n)` is the shared `KPNat U n`.  SUV Theorem 62 (p. 100), recalled on p. 168. -/
theorem KPNat_le_iff_tsum_two_pow_neg_ne_top {U : Map} (hU : IsOptimalPrefixConditional U)
    {f : ℕ → ℕ} (hf : IsUpperSemicomputableNat f) :
    (∃ c : ℕ, ∀ n, KPNat U n ≤ (f n : ENat) + (c : ENat)) ↔
      (∑' n, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ :=
  KPPlain_le_iff_tsum_two_pow_neg_ne_top hU computable_natToBitString
    natToBitString_injective hf

/-- **SUV p. 168.** The coding theorem `K(n) = −log m(n) + O(1)`
translates "the bound `f` is tight infinitely often" into the Solovay property of the
series `2^{-f(n)}`. -/
theorem hasSolovayProperty_two_pow_neg_iff_tight {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {f : ℕ → ℕ} :
    HasSolovayProperty m (fun n => ((2 : ℚ)⁻¹) ^ f n) ↔
      ∃ c : ℕ, {n : ℕ | (f n : ENat) ≤ KPNat U n + (c : ENat)}.Infinite := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hA, hB⟩ := exists_const_KPNat_aprioriNat_equiv hm hU
  constructor
  · rintro ⟨ε, hε, hinf⟩
    obtain ⟨d, hd⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.mul_pos hε.ne' hc₂.ne').ne'
    refine ⟨d, Set.Infinite.mono ?_ hinf⟩
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    refine le_add_nat_of_complexityWeight_le (KPNat_ne_top hU n) ?_
    rw [complexityWeight_coe]
    calc (2 : ℝ≥0∞)⁻¹ ^ d * complexityWeight (KPNat U n)
        ≤ (ε * c₂) * complexityWeight (KPNat U n) := mul_le_mul_left hd.le _
      _ = ε * (c₂ * complexityWeight (KPNat U n)) := by ring
      _ ≤ ε * m n := mul_le_mul_right (hB n) ε
      _ ≤ ENNReal.ofReal ((((2 : ℚ)⁻¹ ^ f n : ℚ) : ℝ)) := hn
      _ = (2 : ℝ≥0∞)⁻¹ ^ f n := ofReal_rat_inv_two_pow _
  · rintro ⟨c, hinf⟩
    refine ⟨c₁ * (2 : ℝ≥0∞)⁻¹ ^ c,
      ENNReal.mul_pos hc₁.ne' (pow_ne_zero _ (by simp)), Set.Infinite.mono ?_ hinf⟩
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 (KPNat_ne_top hU n)
    rw [← hv] at hn
    have hvle : f n ≤ v + c := by exact_mod_cast hn
    have hApp : c₁ * m n ≤ (2 : ℝ≥0∞)⁻¹ ^ v := by
      have hAn := hA n
      rwa [← hv, complexityWeight_coe] at hAn
    calc c₁ * (2 : ℝ≥0∞)⁻¹ ^ c * m n = (2 : ℝ≥0∞)⁻¹ ^ c * (c₁ * m n) := by ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ v := mul_le_mul_right hApp _
      _ = (2 : ℝ≥0∞)⁻¹ ^ (c + v) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ f n := inv_two_pow_antitone (by omega)
      _ = ENNReal.ofReal ((((2 : ℚ)⁻¹ ^ f n : ℚ) : ℝ)) := (ofReal_rat_inv_two_pow _).symm

/-- **SUV p. 165.** Every computable series of nonnegative rationals with finite sum
satisfies `rᵢ = O(m(i))`.

The frozen hypothesis `hr0` turns out to be unnecessary — `ENNReal.ofReal` already clamps a
negative term to `0` — but it is kept, because the statement is frozen. -/
theorem exists_const_le_apriori_of_computable_series {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (_hr0 : ∀ i, 0 ≤ r i)
    (hfin : (∑' i, ENNReal.ofReal ((r i : ℝ))) ≠ ⊤) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∀ i, ENNReal.ofReal ((r i : ℝ)) ≤ c * m i := by
  -- a dyadic bound for the total mass, so that the normalised series is a semimeasure
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (∑' i, ENNReal.ofReal ((r i : ℝ))) ≤ (2 : ℝ≥0∞) ^ d := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
    refine ⟨n, le_trans hn.le ?_⟩
    have hnat : (n : ℕ) ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
    calc (n : ℝ≥0∞) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
      _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring
  have h2ne : ((2 : ℝ≥0∞) ^ d) ≠ 0 := pow_ne_zero _ (by simp)
  have h2top : ((2 : ℝ≥0∞) ^ d) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hsm : IsLowerSemicomputableSemimeasureNat
      (fun i => ENNReal.ofReal ((r i : ℝ)) / (2 : ℝ≥0∞) ^ d) := by
    constructor
    · change (∑' x : BitString,
        ENNReal.ofReal ((r (bitStringToNat x) : ℝ)) / (2 : ℝ≥0∞) ^ d) ≤ 1
      rw [tsum_congr (fun x : BitString => ENNReal.div_eq_inv_mul), ENNReal.tsum_mul_left,
        tsum_comp_bitStringToNat (fun i => ENNReal.ofReal ((r i : ℝ)))]
      calc ((2 : ℝ≥0∞) ^ d)⁻¹ * ∑' i, ENNReal.ofReal ((r i : ℝ))
          ≤ ((2 : ℝ≥0∞) ^ d)⁻¹ * (2 : ℝ≥0∞) ^ d := mul_le_mul_right hd _
        _ = 1 := ENNReal.inv_mul_cancel h2ne h2top
    · exact (isLSC_ofReal_of_computable hr).div_two_pow d
  obtain ⟨c₀, hc₀, hdom⟩ := hm.dominates hsm
  set c₁ : ℝ≥0∞ := min c₀ 1 with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hc₀ (by norm_num)
  have hc₁ne : c₁ ≠ 0 := hc₁pos.ne'
  have hc₁top : c₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(2 : ℝ≥0∞) ^ d * c₁⁻¹, ENNReal.mul_pos h2ne (ENNReal.inv_ne_zero.2 hc₁top),
    ENNReal.mul_ne_top h2top (ENNReal.inv_ne_top.2 hc₁ne), fun i => ?_⟩
  have hstep : c₁ * (ENNReal.ofReal ((r i : ℝ)) / (2 : ℝ≥0∞) ^ d) ≤ m i :=
    le_trans (mul_le_mul_left (min_le_left _ _) _) (hdom i)
  have hid : ((2 : ℝ≥0∞) ^ d * c₁⁻¹) * (c₁ * (ENNReal.ofReal ((r i : ℝ)) / (2 : ℝ≥0∞) ^ d))
      = (c₁⁻¹ * c₁) * ((((2 : ℝ≥0∞) ^ d)⁻¹ * (2 : ℝ≥0∞) ^ d) *
          ENNReal.ofReal ((r i : ℝ))) := by
    rw [ENNReal.div_eq_inv_mul]
    ring
  calc ENNReal.ofReal ((r i : ℝ))
      = ((2 : ℝ≥0∞) ^ d * c₁⁻¹) *
          (c₁ * (ENNReal.ofReal ((r i : ℝ)) / (2 : ℝ≥0∞) ^ d)) := by
        rw [hid, ENNReal.inv_mul_cancel hc₁ne hc₁top, ENNReal.inv_mul_cancel h2ne h2top,
          one_mul, one_mul]
    _ ≤ ((2 : ℝ≥0∞) ^ d * c₁⁻¹) * m i := mul_le_mul_right hstep _

/-- **SUV p. 165.** A *Solovay function* is a computable bound `S(i)` for the prefix
complexity `K(i)` that is tight infinitely often: `K(i) ≤ S(i) + O(1)` for every `i`,
and `K(i) ≥ S(i) - c` for some `c` and infinitely many `i`. -/
def IsSolovayFunction (U : Map) (S : ℕ → ℕ) : Prop :=
  Computable S ∧
  (∃ c : ℕ, ∀ i, KPNat U i ≤ (S i : ENat) + (c : ENat)) ∧
  (∃ c : ℕ, {i : ℕ | (S i : ENat) ≤ KPNat U i + (c : ENat)}.Infinite)

/-- A convergent series of nonnegative rationals has a finite `ℝ≥0∞`-sum: the partial sums
are non-decreasing and bounded by the limit, so the real series is summable. -/
theorem tsum_ofReal_ne_top_of_partialSums_tendsto {r : ℕ → ℚ} (hr0 : ∀ i, 0 ≤ r i) {α : ℝ}
    (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α)) :
    (∑' i, ENNReal.ofReal ((r i : ℝ))) ≠ ⊤ := by
  have hr0' : ∀ i, (0 : ℝ) ≤ ((r i : ℚ) : ℝ) := fun i => by exact_mod_cast hr0 i
  have hmono : Monotone (fun n => (partialSums r n : ℝ)) := by
    intro a b hab
    simp only [partialSums]
    push_cast
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hab))
      (fun i _ _ => hr0' i)
  have hle : ∀ n, (partialSums r n : ℝ) ≤ α := hmono.ge_of_tendsto hsum
  have hsummable : Summable (fun i => ((r i : ℚ) : ℝ)) := by
    refine summable_of_sum_range_le (c := α) hr0' (fun n => ?_)
    have h := hle n
    simpa [partialSums] using h
  rw [← ENNReal.ofReal_tsum_of_nonneg hr0' hsummable]
  exact ENNReal.ofReal_ne_top

/-- **SUV p. 165.** A computable *converging* series `∑ rᵢ` of nonnegative rationals has
the Solovay property if and only if `i ↦ -log₂ rᵢ` is a Solovay function.  The rounding
mentioned in the source is the hypothesis `hround`: `S i = ⌈-log₂ rᵢ⌉`.

The convergence hypothesis `hfin` is essential: dropping the source's
standing hypothesis "*converging* series" (SUV p. 165, first line of §5.7.5: "Consider a
computable **converging** series `∑ rᵢ` of non-negative rational numbers") makes
the forward implication false.  Counterexample: `rᵢ = 1/2` for every `i`, whose rounding
is `S ≡ 1`.  The left-hand side holds — take `ε = 1`; since `∑ᵢ m(i) ≤ 1` at most one index
has `m(i) > 1/2`, so `{i | 1·m(i) ≤ 1/2}` is cofinite, hence infinite.  The right-hand side
fails, because `IsSolovayFunction U S` demands `K(i) ≤ S i + c = 1 + c` for *every* `i`, i.e.
a bounded prefix complexity, which `kpNatSublevel_finite` refutes.  The convergence
hypothesis `hfin` is the source's reading, under which the equivalence holds. -/
theorem hasSolovayProperty_iff_isSolovayFunction {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {r : ℕ → ℚ} (_hr : Computable r) (_hpos : ∀ i, 0 < r i)
    {S : ℕ → ℕ} (hS : Computable S)
    (hround : ∀ i, ((2 : ℝ)⁻¹) ^ S i ≤ (r i : ℝ) ∧ (r i : ℝ) < 2 * ((2 : ℝ)⁻¹) ^ S i)
    (hfin : (∑' i, ENNReal.ofReal ((r i : ℝ))) ≠ ⊤) :
    HasSolovayProperty m r ↔ IsSolovayFunction U S := by
  -- `hr` and `hpos` are kept to mirror the frozen statement; the proof needs neither, since
  -- `hround` already forces `rᵢ > 0` and the computability that matters is that of `S`.
  have hdy : ∀ i, ENNReal.ofReal ((((2 : ℚ)⁻¹ ^ S i : ℚ)) : ℝ) = (2 : ℝ≥0∞)⁻¹ ^ S i :=
    fun i => ofReal_rat_inv_two_pow (S i)
  -- the series and its rounding have the Solovay property simultaneously
  have hequiv : HasSolovayProperty m r ↔ HasSolovayProperty m (fun i => ((2 : ℚ)⁻¹) ^ S i) := by
    constructor
    · rintro ⟨ε, hε, hinf⟩
      refine ⟨ε * (2 : ℝ≥0∞)⁻¹, ENNReal.mul_pos hε.ne' (by simp),
        Set.Infinite.mono ?_ hinf⟩
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      rw [hdy i]
      have hup : ENNReal.ofReal ((r i : ℝ)) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ S i := by
        refine le_trans (ENNReal.ofReal_le_ofReal (hround i).2.le) ?_
        rw [ENNReal.ofReal_mul (by norm_num), ofReal_inv_two_pow]
        norm_num
      calc ε * (2 : ℝ≥0∞)⁻¹ * m i = (2 : ℝ≥0∞)⁻¹ * (ε * m i) := by ring
        _ ≤ (2 : ℝ≥0∞)⁻¹ * (2 * (2 : ℝ≥0∞)⁻¹ ^ S i) := mul_le_mul_right (le_trans hi hup) _
        _ = (2 : ℝ≥0∞)⁻¹ ^ S i := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    · rintro ⟨ε, hε, hinf⟩
      refine ⟨ε, hε, Set.Infinite.mono ?_ hinf⟩
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      rw [hdy i] at hi
      refine le_trans hi ?_
      rw [← ofReal_inv_two_pow (S i)]
      exact ENNReal.ofReal_le_ofReal (hround i).1
  -- the upper-bound clause is automatic under the convergence hypothesis
  have hUSC : IsUpperSemicomputableNat S :=
    ⟨fun _ n => S n, hS.comp Computable.snd, fun _ _ => le_rfl, fun n => ⟨0, fun _ _ => rfl⟩⟩
  have hupper : ∃ c : ℕ, ∀ i, KPNat U i ≤ (S i : ENat) + (c : ENat) := by
    refine (KPNat_le_iff_tsum_two_pow_neg_ne_top hU hUSC).2 ?_
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum (fun n => ?_))
    rw [← ofReal_inv_two_pow (S n)]
    exact ENNReal.ofReal_le_ofReal (hround n).1
  rw [hequiv, hasSolovayProperty_two_pow_neg_iff_tight hm hU]
  exact ⟨fun h => ⟨hS, hupper, h⟩, fun h => h.2.2⟩

/-- A computable converging series of positive rationals has the Solovay property if and
only if its dyadic rounding exponent `S` is a Solovay function; alias of
`hasSolovayProperty_iff_isSolovayFunction`, used by the two existence results
of p. 166.  SUV p. 165. -/
theorem hasSolovayProperty_iff_isSolovayFunction_of_tsum_ne_top {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {U : Map} (hU : IsOptimalPrefixConditional U)
    {r : ℕ → ℚ} (hr : Computable r) (hpos : ∀ i, 0 < r i)
    {S : ℕ → ℕ} (hS : Computable S)
    (hround : ∀ i, ((2 : ℝ)⁻¹) ^ S i ≤ (r i : ℝ) ∧ (r i : ℝ) < 2 * ((2 : ℝ)⁻¹) ^ S i)
    (hfin : (∑' i, ENNReal.ofReal ((r i : ℝ))) ≠ ⊤) :
    HasSolovayProperty m r ↔ IsSolovayFunction U S :=
  hasSolovayProperty_iff_isSolovayFunction hm hU hr hpos hS hround hfin


/-! ### Theorem 111 -/

/-! #### Theorem 111, forward direction, decomposed

SUV p. 166 reads the forward half off Theorem 108 with `hᵢ = ε·m(i)`.  That route is not
available at the frozen statement: `not_isMartinLofRandomReal_of_lscTailCover`
(`Omega/Prediction.lean`) demands a **strictly** increasing approximation, while the
partial sums of a series with `0 ≤ rᵢ` are only non-decreasing (a series with a zero term
has `aᵢ = aᵢ₊₁`), and no hypothesis of Theorem 111 excludes zero terms.  Theorem 109
(p. 164) is the same criterion *without* the `StrictMono` hypothesis, and it is what the
argument really needs: the indices at which the bound `rᵢ = O(m(i))` fails to be tight
form an enumerable co-finite set of small `r`-mass.  So the forward half is Theorem 109
applied to the family `W(ε) = {i | rᵢ < (ε/2)·m(i)}`, and the only new ingredient is that
this family is enumerable. -/

/-- **SUV p. 166.** For a computable series of rationals and a
lower semicomputable semimeasure `m` on `ℕ`, the indices at which the term is small
compared with `m` form a *uniformly enumerable* family.

The factor `1/2` is the slack that turns the bound
`∑_{i ∈ W(ε)} rᵢ ≤ (ε/2)·∑ᵢ m(i) ≤ ε/2` into the **strict** inequality that Theorem 109
asks for; it is not an extra assumption, only a choice of the enumerated threshold. -/
theorem isUniformlyREFamily_lt_apriori {m : ℕ → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r)
    (hr0 : ∀ i, 0 ≤ r i) :
    IsUniformlyREFamily (fun ε : ℚ => {i : ℕ |
      ENNReal.ofReal ((r i : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) * m i}) := by
  classical
  obtain ⟨A, hAmono, hAsup, hAc⟩ := hm.2
  have hBc : Computable (fun p : ℕ × ℕ => A p.1 (natToBitString p.2) ([] : BitString)) :=
    hAc.comp (Computable.fst.pair
      ((computable_natToBitString.comp Computable.snd).pair (Computable.const [])))
  have hBsup : ∀ i : ℕ, (⨆ s : ℕ, dyadicValue (A s (natToBitString i) []) s) = m i := by
    intro i
    simpa using hAsup (natToBitString i) []
  -- the `ℝ≥0∞` inequality is the `Σ₁` rational stage test
  have hkey : ∀ (ε : ℚ) (i : ℕ),
      (ENNReal.ofReal ((r i : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) * m i) ↔
        ∃ s : ℕ, r i < (ε / 2) * ((A s (natToBitString i) [] : ℚ) * ((2 : ℚ)⁻¹) ^ s) := by
    intro ε i
    have hri : (0 : ℝ) ≤ ((r i : ℚ) : ℝ) := by exact_mod_cast hr0 i
    by_cases hεpos : 0 < ε
    swap
    · have hε : ε ≤ 0 := not_lt.1 hεpos
      constructor
      · intro hlt
        exfalso
        have hz : ENNReal.ofReal ((ε : ℝ) / 2) = 0 := by
          refine ENNReal.ofReal_eq_zero.2 ?_
          have hεR : ((ε : ℝ)) ≤ 0 := by exact_mod_cast hε
          linarith
        rw [hz, zero_mul] at hlt
        exact absurd hlt (not_lt.2 (zero_le))
      · rintro ⟨s, hs⟩
        exfalso
        have hnn : (0 : ℚ) ≤ ((A s (natToBitString i) [] : ℚ) * ((2 : ℚ)⁻¹) ^ s) := by positivity
        have hle : (ε / 2) * ((A s (natToBitString i) [] : ℚ) * ((2 : ℚ)⁻¹) ^ s) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
        exact absurd hs (not_lt.2 (le_trans hle (hr0 i)))
    · rw [← hBsup i, ENNReal.mul_iSup, lt_iSup_iff]
      refine exists_congr (fun s => ?_)
      have hεR : (0 : ℝ) ≤ (ε : ℝ) / 2 := by
        have h : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hεpos
        linarith
      have hcast : (((ε / 2) * ((A s (natToBitString i) [] : ℚ) * ((2 : ℚ)⁻¹) ^ s) : ℚ) : ℝ)
          = ((ε : ℝ) / 2) * ((A s (natToBitString i) [] : ℝ) * ((2 : ℝ)⁻¹) ^ s) := by
        push_cast
        ring
      have hdv : ENNReal.ofReal ((ε : ℝ) / 2) * dyadicValue (A s (natToBitString i) []) s
          = ENNReal.ofReal ((((ε / 2) *
              ((A s (natToBitString i) [] : ℚ) * ((2 : ℚ)⁻¹) ^ s) : ℚ)) : ℝ) := by
        rw [hcast, ENNReal.ofReal_mul hεR, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num [dyadicValue, div_eq_mul_inv, ENNReal.inv_pow]
      rw [hdv, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hri]
      exact Rat.cast_lt
  refine ⟨fun ε k =>
    bif decide ((ε / 2) * ((A k.unpair.2 (natToBitString k.unpair.1) [] : ℚ)
        * ((2 : ℚ)⁻¹) ^ k.unpair.2) ≤ r k.unpair.1)
      then none else some k.unpair.1, ?_, ?_⟩
  · have hidx : Computable (fun p : ℚ × ℕ => p.2.unpair.1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hstage : Computable (fun p : ℚ × ℕ => p.2.unpair.2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hA : Computable (fun p : ℚ × ℕ =>
        A p.2.unpair.2 (natToBitString p.2.unpair.1) ([] : BitString)) :=
      hBc.comp (hstage.pair hidx)
    have hval : Computable (fun p : ℚ × ℕ =>
        (p.1 / 2) * ((A p.2.unpair.2 (natToBitString p.2.unpair.1) [] : ℚ)
          * ((2 : ℚ)⁻¹) ^ p.2.unpair.2)) :=
      computable₂_ratMul.comp (computable_ratHalf.comp Computable.fst)
        (computable₂_ratMul.comp (computable_nat_to_rat.comp hA)
          (computable_inv_two_pow_rat.comp hstage))
    exact Computable.cond (computable_ratLe.comp hval (hr.comp hidx))
      (Computable.const none) (Computable.option_some.comp hidx)
  · intro ε n
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hn
      obtain ⟨s, hs⟩ := (hkey ε n).1 hn
      refine ⟨Nat.pair n s, ?_⟩
      simp only [Nat.unpair_pair]
      rw [decide_eq_false (not_le.2 hs), cond_false]
    · rintro ⟨k, hk⟩
      refine (hkey ε n).2 ⟨k.unpair.2, ?_⟩
      by_cases hc : (ε / 2) * ((A k.unpair.2 (natToBitString k.unpair.1) [] : ℚ)
          * ((2 : ℚ)⁻¹) ^ k.unpair.2) ≤ r k.unpair.1
      · rw [decide_eq_true hc, cond_true] at hk
        exact absurd hk (by simp)
      · rw [decide_eq_false hc, cond_false, Option.some.injEq] at hk
        subst hk
        exact not_le.1 hc

/-- If `rᵢ/m(i) → 0` then the sum is not random. *Proof.* Theorem 109 (`Omega/Prediction.lean`)
applied to `W(ε) = {i | rᵢ < (ε/2)·m(i)}`. That family is enumerable
(`isUniformlyREFamily_lt_apriori`); its `r`-mass is at most `(ε/2)·∑ᵢ m(i) ≤ ε/2 < ε`
because `m` is a semimeasure; and its complement `{i | (ε/2)·m(i) ≤ rᵢ}` is finite — this is
literally the hypothesis `RatioTendstoZero m r` at the threshold `ε/2`.  SUV Theorem 111
(Section 5.7, p. 165), forward direction. -/
theorem not_isMartinLofRandomReal_of_ratioTendstoZero {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : RatioTendstoZero m r) : ¬ IsMartinLofRandomReal α := by
  have hsum' : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ))
      Filter.atTop (nhds α) := by
    refine hsum.congr (fun n => ?_)
    simp [partialSums]
  refine not_isMartinLofRandomReal_of_exists_smallMassREFamily hr hr0 hsum' ?_
  refine ⟨fun ε : ℚ => {i : ℕ |
      ENNReal.ofReal ((r i : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) * m i},
    isUniformlyREFamily_lt_apriori hm.isLowerSemicomputableSemimeasureNat hr hr0,
    fun ε hε => ?_⟩
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hhalf : (0 : ℝ) < (ε : ℝ) / 2 := by linarith
  refine ⟨?_, ?_⟩
  · calc (∑' i : ({i : ℕ |
              ENNReal.ofReal ((r i : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) * m i} : Set ℕ),
            ENNReal.ofReal ((r (i : ℕ) : ℝ)))
        ≤ ∑' i : ({i : ℕ |
              ENNReal.ofReal ((r i : ℝ)) < ENNReal.ofReal ((ε : ℝ) / 2) * m i} : Set ℕ),
            ENNReal.ofReal ((ε : ℝ) / 2) * m (i : ℕ) :=
          ENNReal.tsum_le_tsum (fun i => le_of_lt i.2)
      _ ≤ ∑' i : ℕ, ENNReal.ofReal ((ε : ℝ) / 2) * m i :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ENNReal.ofReal ((ε : ℝ) / 2) * ∑' i : ℕ, m i := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal ((ε : ℝ) / 2) * 1 := mul_le_mul_right hm.tsum_le_one _
      _ = ENNReal.ofReal ((ε : ℝ) / 2) := mul_one _
      _ < ENNReal.ofReal ((ε : ℝ)) := (ENNReal.ofReal_lt_ofReal_iff hεR).2 (by linarith)
  · refine (h (ENNReal.ofReal ((ε : ℝ) / 2)) (ENNReal.ofReal_pos.2 hhalf)).subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq, not_lt] at hi ⊢
    exact hi

/-- Computability of the stage-by-stage dyadic floor approximation of the guarded scaled
term sequence in `exists_const_two_pow_mul_le_apriori_of_reFamily`. -/
private lemma dyadicFloor_approx_computable_of_reFamily {r : ℕ → ℚ} (hr : Computable r)
    {e : ℚ → ℕ → Option ℕ} (hec : Computable₂ e) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      bif ((List.range p.2.1).map (fun t => e (((2 : ℚ)⁻¹) ^ (2 * p.1)) t)).foldr
        (fun o b => decide (o = some (bitStringToNat p.2.2.1)) || b) false
      then ratDyadicFloor (((2 : ℚ) ^ (2 * p.1)) * r (bitStringToNat p.2.2.1)) p.2.1
      else 0) := by
  have hs : Computable (fun p : ℕ × ℕ × BitString × BitString => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hidx : Computable (fun p : ℕ × ℕ × BitString × BitString => bitStringToNat p.2.2.1) :=
    computable_bitStringToNat.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have heps : Computable (fun p : ℕ × ℕ × BitString × BitString => ((2 : ℚ)⁻¹) ^ (2 * p.1)) :=
    (computable_inv_two_pow_rat.comp
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst).to_comp)).of_eq (fun _ => rfl)
  have hlist : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      (List.range p.2.1).map (fun t => e (((2 : ℚ)⁻¹) ^ (2 * p.1)) t)) :=
    Computable.list_map (Primrec.list_range.to_comp.comp hs)
      (hec.comp (heps.comp Computable.fst) Computable.snd)
  have hstep : Computable₂ (fun (p : ℕ × ℕ × BitString × BitString) (z : Option ℕ × Bool) =>
      decide (z.1 = some (bitStringToNat p.2.2.1)) || z.2) := by
    have hEq : Primrec (fun w : (ℕ × ℕ × BitString × BitString) × (Option ℕ × Bool) =>
        decide (w.2.1 = some (bitStringToNat w.1.2.2.1))) :=
      PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp Primrec.snd)
        (Primrec.option_some.comp (primrec_bitStringToNat.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
    exact (Primrec.or.comp hEq (Primrec.snd.comp Primrec.snd)).to_comp
  have hguard : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      ((List.range p.2.1).map (fun t => e (((2 : ℚ)⁻¹) ^ (2 * p.1)) t)).foldr
        (fun o b => decide (o = some (bitStringToNat p.2.2.1)) || b) false) :=
    (Computable.list_foldr hlist (Computable.const false) hstep).of_eq (fun _ => rfl)
  have hval : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      ((2 : ℚ) ^ (2 * p.1)) * r (bitStringToNat p.2.2.1)) :=
    (computable₂_ratMul.comp
      (computable_two_pow_rat.comp ((Primrec.nat_mul.comp (Primrec.const 2)
        Primrec.fst).to_comp)) (hr.comp hidx)).of_eq (fun _ => rfl)
  have hthen : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      ratDyadicFloor (((2 : ℚ) ^ (2 * p.1)) * r (bitStringToNat p.2.2.1)) p.2.1) :=
    computable_ratDyadicFloor.comp hval hs
  exact (Computable.cond hguard hthen (Computable.const 0)).of_eq (fun _ => rfl)

open Classical in
/-- Total mass bound for the guarded scaled term sequence in
`exists_const_two_pow_mul_le_apriori_of_reFamily`. -/
private lemma tsum_indicator_qq_le_one {r : ℕ → ℚ} {W : ℚ → Set ℕ}
    (hsmall : ∀ ε : ℚ, 0 < ε →
      (∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) < ENNReal.ofReal (ε : ℝ))
    (k : ℕ) :
    (∑' i : ℕ, Set.indicator (W (((2 : ℚ)⁻¹) ^ (2 * k)))
      (fun i => ENNReal.ofReal ((((((2 : ℚ) ^ (2 * k)) * r i : ℚ)) : ℝ))) i) ≤ 1 := by
  set ee : ℚ := ((2 : ℚ)⁻¹) ^ (2 * k) with hee
  set qq : ℕ → ℚ := fun i => ((2 : ℚ) ^ (2 * k)) * r i with hqq
  rw [← tsum_subtype]
  have hsplit : ∀ i : (W ee : Set ℕ),
      ENNReal.ofReal ((qq (i : ℕ) : ℚ) : ℝ)
        = ENNReal.ofReal ((((2 : ℚ) ^ (2 * k) : ℚ)) : ℝ)
          * ENNReal.ofReal ((r (i : ℕ) : ℝ)) := by
    intro i
    rw [hqq]
    simp only
    push_cast
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [tsum_congr hsplit, ENNReal.tsum_mul_left]
  have hepos : (0 : ℚ) < ee := by rw [hee]; positivity
  calc ENNReal.ofReal ((((2 : ℚ) ^ (2 * k) : ℚ)) : ℝ)
        * ∑' i : (W ee : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))
      ≤ ENNReal.ofReal ((((2 : ℚ) ^ (2 * k) : ℚ)) : ℝ)
        * ENNReal.ofReal ((ee : ℚ) : ℝ) :=
        mul_le_mul_right (hsmall ee hepos).le _
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have hprod : (((2 : ℚ) ^ (2 * k) : ℚ) : ℝ) * ((ee : ℚ) : ℝ) = 1 := by
          rw [hee]; push_cast; rw [← mul_pow]; norm_num
        rw [hprod, ENNReal.ofReal_one]

open Classical in
/-- Evaluation of `dyadicWeight k` times the indicator term when `i ∈ W (2^{-2k})`. -/
private lemma dyadicWeight_mul_indicator_qq_eq (k i : ℕ) {r : ℕ → ℚ} {W : ℚ → Set ℕ}
    (hi : i ∈ W (((2 : ℚ)⁻¹) ^ (2 * k))) :
    dyadicWeight k * (if i ∈ W (((2 : ℚ)⁻¹) ^ (2 * k))
      then ENNReal.ofReal ((((((2 : ℚ) ^ (2 * k)) * r i : ℚ)) : ℝ)) else 0)
      = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ))) := by
  rw [if_pos hi]
  have hcast : ENNReal.ofReal (((((2 : ℚ) ^ (2 * k)) * r i : ℚ)) : ℝ)
      = (2 : ℝ≥0∞) ^ (2 * k) * ENNReal.ofReal ((r i : ℝ)) := by
    push_cast
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hcast, dyadicWeight]
  have hcancel : ((2 : ℝ≥0∞)⁻¹) ^ k * (2 : ℝ≥0∞) ^ k = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  calc ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * ((2 : ℝ≥0∞) ^ (2 * k) * ENNReal.ofReal ((r i : ℝ)))
      = (((2 : ℝ≥0∞)⁻¹) ^ k * (2 : ℝ≥0∞) ^ k) *
          ((2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ)))) := by
        rw [pow_succ, two_mul, pow_add]
        ring
    _ = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ))) := by
        rw [hcancel, one_mul]

/-- **SUV p. 166, the covered-intervals semimeasures `Mₙ`.**  If for
every `ε > 0` an enumerable set `W(ε)` of indices carries `r`-mass below `ε`, then the a priori
probability dominates the `2ᵏ`-scaled terms on `W(2^{-2k})`, uniformly in `k`.

This is the one construction of the reverse half of Theorem 111, isolated: the source builds
`Mₙ(i) = 2ⁿ·rᵢ` on the covered indices, notes `∑ᵢ Mₙ(i) ≤ 2^{-n}`, and sums over `n`.

The frozen-style hypothesis `hr0` is kept for symmetry with the rest of the file but is not
used: `ENNReal.ofReal` already clamps a negative term to `0`. -/
theorem exists_const_two_pow_mul_le_apriori_of_reFamily {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (_hr0 : ∀ i, 0 ≤ r i)
    {W : ℚ → Set ℕ} (hW : IsUniformlyREFamily W)
    (hsmall : ∀ ε : ℚ, 0 < ε →
      (∑' i : (W ε : Set ℕ), ENNReal.ofReal ((r (i : ℕ) : ℝ))) < ENNReal.ofReal (ε : ℝ)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ (k i : ℕ), i ∈ W (((2 : ℚ)⁻¹) ^ (2 * k)) →
      c * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ))) ≤ m i := by
  classical
  obtain ⟨e, hec, hespec⟩ := hW
  set ee : ℕ → ℚ := fun k => ((2 : ℚ)⁻¹) ^ (2 * k) with hee
  set qq : ℕ → ℕ → ℚ := fun k i => ((2 : ℚ) ^ (2 * k)) * r i with hqq
  set G : ℕ → ℕ → ℕ → Bool := fun k i s =>
    ((List.range s).map (fun t => e (ee k) t)).foldr
      (fun o b => decide (o = some i) || b) false with hG
  set mu : ℕ → ℕ → ℝ≥0∞ := fun k i =>
    if i ∈ W (ee k) then ENNReal.ofReal (((qq k i : ℚ)) : ℝ) else 0 with hmu
  set Aa : ℕ → ℕ → BitString → BitString → ℕ := fun k s out _ =>
    bif G k (bitStringToNat out) s then ratDyadicFloor (qq k (bitStringToNat out)) s
    else 0 with hAa
  -- the guard is a bounded search through the enumerator
  have hGiff : ∀ k i s, G k i s = true ↔ ∃ t < s, e (ee k) t = some i := by
    intro k i s
    rw [hG]
    simp only
    rw [foldr_or_eq_true_iff]
    constructor
    · rintro ⟨o, hoin, hoeq⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hoin
      exact ⟨t, List.mem_range.1 ht, by simpa using hoeq⟩
    · rintro ⟨t, hts, hte⟩
      exact ⟨some i, List.mem_map.2 ⟨t, List.mem_range.2 hts, hte⟩, by simp⟩
  have hGmono : ∀ k i s s', s ≤ s' → G k i s = true → G k i s' = true := by
    intro k i s s' hss hGs
    obtain ⟨t, hts, hte⟩ := (hGiff k i s).1 hGs
    exact (hGiff k i s').2 ⟨t, lt_of_lt_of_le hts hss, hte⟩
  have hGex : ∀ k i, (∃ s, G k i s = true) ↔ i ∈ W (ee k) := by
    intro k i
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨t, -, hte⟩ := (hGiff k i s).1 hs
      exact (hespec _ _).2 ⟨t, hte⟩
    · intro hi
      obtain ⟨t, hte⟩ := (hespec _ _).1 hi
      exact ⟨t + 1, (hGiff k i (t + 1)).2 ⟨t, Nat.lt_succ_self t, hte⟩⟩
  -- the approximation is monotone in the stage
  have hAmono : ∀ (k s : ℕ) (out ctx : BitString),
      dyadicValue (Aa k s out ctx) s ≤ dyadicValue (Aa k (s + 1) out ctx) (s + 1) := by
    intro k s out ctx
    rw [hAa]
    simp only
    by_cases hGs : G k (bitStringToNat out) s = true
    · rw [hGs, hGmono k (bitStringToNat out) s (s + 1) (Nat.le_succ s) hGs]
      simpa using dyadicValue_ratDyadicFloor_mono_of_le
        (le_refl (qq k (bitStringToNat out))) s
    · rw [Bool.not_eq_true] at hGs
      rw [hGs]
      simp [dyadicValue]
  -- the approximation converges to the guarded scaled term
  have hAsup : ∀ (k : ℕ) (out ctx : BitString),
      (⨆ s, dyadicValue (Aa k s out ctx) s) = mu k (bitStringToNat out) := by
    intro k out ctx
    have hfloor : (⨆ s, dyadicValue (ratDyadicFloor (qq k (bitStringToNat out)) s) s)
        = ENNReal.ofReal ((qq k (bitStringToNat out) : ℚ) : ℝ) := by
      have h := iSup_dyadicValue_ratDyadicFloor
        (f := fun _ : ℕ => qq k (bitStringToNat out)) monotone_const
      simpa using h
    rw [hmu]
    simp only
    by_cases hmem : (bitStringToNat out) ∈ W (ee k)
    · rw [if_pos hmem, ← hfloor]
      obtain ⟨s₀, hs₀⟩ := (hGex k (bitStringToNat out)).2 hmem
      refine le_antisymm (iSup_le fun s => ?_) (iSup_le fun s => ?_)
      · refine le_iSup_of_le s ?_
        rw [hAa]
        simp only
        by_cases hGs : G k (bitStringToNat out) s = true
        · rw [hGs]; simp
        · rw [Bool.not_eq_true] at hGs; rw [hGs]; simp [dyadicValue]
      · refine le_iSup_of_le (max s s₀) ?_
        have hGm : G k (bitStringToNat out) (max s s₀) = true :=
          hGmono k (bitStringToNat out) s₀ (max s s₀) (le_max_right _ _) hs₀
        have hstep : dyadicValue (ratDyadicFloor (qq k (bitStringToNat out)) s) s
            ≤ dyadicValue (ratDyadicFloor (qq k (bitStringToNat out)) (max s s₀)) (max s s₀) :=
          dyadicValue_ratDyadicFloor_monotone (f := fun _ => qq k (bitStringToNat out))
            (fun _ => le_refl _) (le_max_left s s₀)
        refine le_trans hstep ?_
        rw [hAa]; simp only; rw [hGm]; simp
    · rw [if_neg hmem]
      refine le_antisymm (iSup_le fun s => ?_) (zero_le)
      have hGs : G k (bitStringToNat out) s = false := by
        rw [← Bool.not_eq_true]
        intro hcon
        exact hmem ((hGex k (bitStringToNat out)).1 ⟨s, hcon⟩)
      rw [hAa]; simp only; rw [hGs]; simp [dyadicValue]
  -- the approximation is computable
  have hAc : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      Aa p.1 p.2.1 p.2.2.1 p.2.2.2) := dyadicFloor_approx_computable_of_reFamily hr hec
  -- the mixture is a lower semicomputable semimeasure
  have hsm : IsLowerSemicomputableSemimeasureNat
      (fun i => ∑' k : ℕ, dyadicWeight k * mu k i) := by
    constructor
    · change (∑' x : BitString, ∑' k : ℕ, dyadicWeight k * mu k (bitStringToNat x)) ≤ 1
      rw [tsum_comp_bitStringToNat (fun i => ∑' k : ℕ, dyadicWeight k * mu k i),
        ENNReal.tsum_comm]
      have hrow : ∀ k : ℕ, (∑' i : ℕ, dyadicWeight k * mu k i) ≤ dyadicWeight k := by
        intro k
        rw [ENNReal.tsum_mul_left]
        have hmass : (∑' i : ℕ, mu k i) ≤ 1 := by
          have hind : ∀ i : ℕ, mu k i
              = Set.indicator (W (ee k))
                (fun i => ENNReal.ofReal ((((((2 : ℚ) ^ (2 * k)) * r i : ℚ)) : ℝ))) i := by
            intro i
            rw [hmu, Set.indicator_apply]
          rw [tsum_congr hind]
          exact tsum_indicator_qq_le_one hsmall k
        calc dyadicWeight k * ∑' i : ℕ, mu k i ≤ dyadicWeight k * 1 :=
              mul_le_mul_right hmass _
          _ = dyadicWeight k := mul_one _
      calc (∑' k : ℕ, ∑' i : ℕ, dyadicWeight k * mu k i)
          ≤ ∑' k : ℕ, dyadicWeight k := ENNReal.tsum_le_tsum hrow
        _ = 1 := tsum_dyadicWeight
    · exact isLSC_unaryMixture_dyadicWeight_of_uniform
        (fun k out _ => mu k (bitStringToNat out)) Aa hAmono hAsup hAc
  obtain ⟨c, hc, hdom⟩ := hm.dominates hsm
  refine ⟨c * (2 : ℝ≥0∞)⁻¹, ENNReal.mul_pos hc.ne' (by simp), fun k i hi => ?_⟩
  have hterm : dyadicWeight k * mu k i
      = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ))) :=
    dyadicWeight_mul_indicator_qq_eq k i hi
  calc c * (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ)))
      = c * (dyadicWeight k * mu k i) := by rw [hterm]; ring
    _ ≤ c * ∑' k' : ℕ, dyadicWeight k' * mu k' i := mul_le_mul_right (ENNReal.le_tsum k) _
    _ ≤ m i := hdom i

/-- If the sum is not random then `rᵢ/m(i) → 0`. *Proof.* Theorem 109
(p. 164, `Omega/Prediction.lean`) turns non-randomness into an enumerable co-finite family
`W(ε)` of `r`-mass below `ε`; `exists_const_two_pow_mul_le_apriori_of_reFamily` turns that
family into the domination `c·2ᵏ·rᵢ ≤ m(i)` on `W(2^{-2k})`. Given `ε > 0` pick `k` with
`2^{-k} < c·ε`: then every index outside the *finite* complement of `W(2^{-2k})` satisfies
`rᵢ < ε·m(i)`, because otherwise `c·2ᵏ·ε·m(i) ≤ m(i)` would force `c·2ᵏ·ε ≤ 1`,
contradicting the choice of `k`. Cancelling `m(i)` uses that it is finite and non-zero
(`apriori_ne_top`, `apriori_pos_of_universal`).  SUV Theorem 111 (Section 5.7, p. 165),
reverse direction. -/
theorem ratioTendstoZero_of_not_isMartinLofRandomReal {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : ¬ IsMartinLofRandomReal α) : RatioTendstoZero m r := by
  have hsum' : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (r i : ℝ))
      Filter.atTop (nhds α) := by
    refine hsum.congr (fun n => ?_)
    simp [partialSums]
  obtain ⟨W, hW, hWspec⟩ := exists_smallMassREFamily_of_not_isMartinLofRandomReal hr hr0 hsum' h
  obtain ⟨c, hc, hdom⟩ := exists_const_two_pow_mul_le_apriori_of_reFamily hm hr hr0 hW
    (fun δ hδ => (hWspec δ hδ).1)
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.mul_pos hc.ne' hε.ne').ne'
  have hqpos : (0 : ℚ) < ((2 : ℚ)⁻¹) ^ (2 * k) := by positivity
  refine Set.Finite.subset ((hWspec (((2 : ℚ)⁻¹) ^ (2 * k)) hqpos).2) ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  intro hiW
  have hmne : m i ≠ 0 := (apriori_pos_of_universal hm i).ne'
  have hmtop : m i ≠ ⊤ := apriori_ne_top hm i
  have hchain : m i * (c * (2 : ℝ≥0∞) ^ k * ε) ≤ m i * 1 := by
    rw [mul_one]
    calc m i * (c * (2 : ℝ≥0∞) ^ k * ε) = c * ((2 : ℝ≥0∞) ^ k * (ε * m i)) := by ring
      _ ≤ c * ((2 : ℝ≥0∞) ^ k * ENNReal.ofReal ((r i : ℝ))) := by gcongr
      _ ≤ m i := hdom k i hiW
  have hle1 : c * (2 : ℝ≥0∞) ^ k * ε ≤ 1 :=
    (ENNReal.mul_le_mul_iff_right hmne hmtop).1 hchain
  have hgt : 1 < c * (2 : ℝ≥0∞) ^ k * ε := by
    have h1 := ENNReal.mul_lt_mul_right (pow_ne_zero k (by simp : (2 : ℝ≥0∞) ≠ 0))
      (ENNReal.pow_ne_top (by simp)) hk
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow] at h1
    calc (1 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ k * (c * ε) := h1
      _ = c * (2 : ℝ≥0∞) ^ k * ε := by ring
  exact absurd hle1 (not_le.2 hgt)

/-- Let `α = ∑ rᵢ` be a computable converging series of nonnegative rational numbers. The number
`α` is random if and only if this series converges slowly in the Solovay sense.  SUV Theorem
111 (Section 5.7, p. 165). -/
theorem isMartinLofRandomReal_iff_hasSolovayProperty {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α)) :
    IsMartinLofRandomReal α ↔ HasSolovayProperty m r := by
  constructor
  · intro hrand
    by_contra hns
    exact not_isMartinLofRandomReal_of_ratioTendstoZero hm hr hr0 hsum
      ((not_hasSolovayProperty_iff m r).1 hns) hrand
  · intro hs
    by_contra hnr
    exact ((not_hasSolovayProperty_iff m r).2
      (ratioTendstoZero_of_not_isMartinLofRandomReal hm hr hr0 hsum hnr)) hs

/-- **SUV p. 165, second proof of Theorem 111's forward half.** A fast (non-Solovay)
converging series has a non-complete sum: `α ≼_c ∑ m(i)` for arbitrarily small `c`,
which for a complete `α` would force `2α ≼₁ α` and hence computability of `α`. -/
theorem not_isSolovayComplete_of_ratioTendstoZero {m : ℕ → ℝ≥0∞}
    (hm : IsUniversalSemimeasureNat m) {r : ℕ → ℚ} (hr : Computable r) (hr0 : ∀ i, 0 ≤ r i)
    {α : ℝ} (hsum : Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α))
    (h : RatioTendstoZero m r) : ¬ IsSolovayComplete α := fun hcomplete =>
  not_isMartinLofRandomReal_of_ratioTendstoZero hm hr hr0 hsum h
    (isMartinLofRandomReal_of_isSolovayComplete hcomplete)

/-! #### Existence of Solovay functions, decomposed (SUV p. 166)

The source derives the existence of Solovay functions from Theorem 111: *take a
computable series of rational numbers with random sum*, and read off `-log₂ rᵢ`.  Below,
that derivation is carried out; what remains are the two evident ingredients — such a
series exists, and the rounding `⌈-log₂ rᵢ⌉` is computable. -/

/-- **SUV p. 166, "take a computable series … with random sum".** There is a computable series of
rationals in `(0,1)` whose sum is an ML-random real. -/
theorem exists_computable_series_isMartinLofRandomReal_sum :
    ∃ (r : ℕ → ℚ) (α : ℝ), Computable r ∧ (∀ i, 0 < r i ∧ r i < 1) ∧
      Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α) ∧
      IsMartinLofRandomReal α := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  obtain ⟨a⟩ := exists_lowerApprox_of_isLowerSemicomputableReal
    (isLowerSemicomputableReal_omegaReal hm)
  obtain ⟨hΩ0, hΩ1⟩ := omegaReal_mem_Ioo hm
  have hmono : Monotone (fun n : ℕ => ((a.seq n : ℚ) : ℝ)) := by
    intro i j hij
    change ((a.seq i : ℚ) : ℝ) ≤ ((a.seq j : ℚ) : ℝ)
    exact_mod_cast a.isStrictMono.monotone hij
  have hle : ∀ i, ((a.seq i : ℚ) : ℝ) ≤ omegaReal m := hmono.ge_of_tendsto a.tendsto
  -- a cut-off index past which the approximation is already positive
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 a.tendsto (omegaReal m) hΩ0
  have hNpos : (0 : ℝ) < ((a.seq N : ℚ) : ℝ) := by
    have h := hN N le_rfl
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  refine ⟨fun i => a.seq (i + 1 + N) - a.seq (i + N),
    omegaReal m - ((a.seq N : ℚ) : ℝ), ?_, fun i => ?_, ?_, ?_⟩
  · have hc1 : Computable (fun i : ℕ => a.seq (i + 1 + N)) :=
      a.isComputable.comp ((Primrec.nat_add.comp
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (Primrec.const N)).to_comp)
    have hc2 : Computable (fun i : ℕ => a.seq (i + N)) :=
      a.isComputable.comp ((Primrec.nat_add.comp Primrec.id (Primrec.const N)).to_comp)
    exact computable₂_ratSub.comp hc1 hc2
  · have hstep : a.seq (i + N) < a.seq (i + 1 + N) := a.isStrictMono (by omega)
    have hbase : ((a.seq N : ℚ) : ℝ) ≤ ((a.seq (i + N) : ℚ) : ℝ) :=
      hmono (by omega)
    refine ⟨by linarith [hstep], ?_⟩
    have hup : ((a.seq (i + 1 + N) : ℚ) : ℝ) - ((a.seq (i + N) : ℚ) : ℝ) < 1 := by
      have := hle (i + 1 + N)
      linarith
    have : ((a.seq (i + 1 + N) - a.seq (i + N) : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have htend : Filter.Tendsto (fun n : ℕ => ((a.seq (n + N) : ℚ) : ℝ)) Filter.atTop
        (nhds (omegaReal m)) := a.tendsto.comp (Filter.tendsto_add_atTop_nat N)
    refine (htend.sub (tendsto_const_nhds (x := ((a.seq N : ℚ) : ℝ)))).congr (fun n => ?_)
    simp only [partialSums]
    rw [Finset.sum_range_sub (f := fun i : ℕ => a.seq (i + N)) n]
    push_cast
    simp
  · have heq : (omegaReal m - ((a.seq N : ℚ) : ℝ)) + ((a.seq N : ℚ) : ℝ) = omegaReal m := by
      ring
    exact (isMartinLofRandomReal_add_rat _ (a.seq N)).1
      (by rw [heq]; exact isMartinLofRandomReal_omegaReal hm)

/-- **SUV p. 166, "make this series non-increasing … by splitting too big
terms into small pieces".** The series of the previous leaf can be chosen
*non-increasing*. -/
theorem exists_antitone_computable_series_isMartinLofRandomReal_sum :
    ∃ (r : ℕ → ℚ) (α : ℝ), Computable r ∧ (∀ i, 0 < r i ∧ r i < 1) ∧ Antitone r ∧
      Filter.Tendsto (fun n => (partialSums r n : ℝ)) Filter.atTop (nhds α) ∧
      IsMartinLofRandomReal α := by
  obtain ⟨u, α, hu, hu01, hsum, hrand⟩ := exists_computable_series_isMartinLofRandomReal_sum
  have hupos : ∀ n, 0 < u n := fun n => (hu01 n).1
  refine ⟨blkSeries u, α, computable_blkSeries hu,
    fun i => ⟨blkSeries_pos hupos i, blkSeries_lt_one hupos (fun n => (hu01 n).2) i⟩,
    blkSeries_antitone hupos, ?_, hrand⟩
  have hsum' : Filter.Tendsto (fun n => ((ratRangeSum u n : ℚ) : ℝ)) Filter.atTop (nhds α) :=
    Filter.Tendsto.congr (fun n => by rw [partialSums_eq_ratRangeSum]) hsum
  exact Filter.Tendsto.congr (fun n => by rw [partialSums_eq_ratRangeSum])
    (tendsto_ratRangeSum_blkSeries hupos hsum')

/-- **SUV p. 165, "some rounding is needed".** For a computable series
of rationals in `(0,1)` the rounded logarithm `S i = ⌈-log₂ rᵢ⌉` is computable and
satisfies the two-sided dyadic bound required by
`hasSolovayProperty_iff_isSolovayFunction`. -/
theorem exists_computable_dyadicRounding {r : ℕ → ℚ} (hr : Computable r)
    (hr01 : ∀ i, 0 < r i ∧ r i < 1) :
    ∃ S : ℕ → ℕ, Computable S ∧
      ∀ i, ((2 : ℝ)⁻¹) ^ S i ≤ (r i : ℝ) ∧ (r i : ℝ) < 2 * ((2 : ℝ)⁻¹) ^ S i := by
  have hex : ∀ i : ℕ, ∃ n : ℕ, ((2 : ℚ)⁻¹) ^ n ≤ r i := by
    intro i
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hr01 i).1 (show ((2 : ℚ)⁻¹) < 1 by norm_num)
    exact ⟨n, hn.le⟩
  refine ⟨fun i => Nat.find (hex i), ?_, fun i => ?_⟩
  · refine Computable.natFind (P := fun i n => ((2 : ℚ)⁻¹) ^ n ≤ r i) ?_ hex
    exact computable_ratLe.comp (computable_inv_two_pow_rat.comp Computable.snd)
      (hr.comp Computable.fst)
  · have hspec : ((2 : ℚ)⁻¹) ^ (Nat.find (hex i)) ≤ r i := Nat.find_spec (hex i)
    have hkpos : 0 < Nat.find (hex i) := by
      rcases Nat.eq_zero_or_pos (Nat.find (hex i)) with h0 | h
      · rw [h0, pow_zero] at hspec
        exact absurd (lt_of_lt_of_le (hr01 i).2 hspec) (lt_irrefl _)
      · exact h
    have hmin : ¬ (((2 : ℚ)⁻¹) ^ (Nat.find (hex i) - 1) ≤ r i) :=
      Nat.find_min (hex i) (by omega)
    push Not at hmin
    have hpow : ((2 : ℚ)⁻¹) ^ (Nat.find (hex i) - 1)
        = 2 * ((2 : ℚ)⁻¹) ^ (Nat.find (hex i)) := by
      obtain ⟨j, hj⟩ : ∃ j, Nat.find (hex i) = j + 1 := ⟨Nat.find (hex i) - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel, pow_succ]
      ring
    rw [hpow] at hmin
    constructor
    · have hc : ((2 : ℝ)⁻¹) ^ (Nat.find (hex i))
          = (((((2 : ℚ)⁻¹) ^ (Nat.find (hex i))) : ℚ) : ℝ) := by push_cast; ring
      rw [hc]
      exact_mod_cast hspec
    · have hc : (2 : ℝ) * ((2 : ℝ)⁻¹) ^ (Nat.find (hex i))
          = ((((2 : ℚ) * ((2 : ℚ)⁻¹) ^ (Nat.find (hex i))) : ℚ) : ℝ) := by push_cast; ring
      rw [hc]
      exact_mod_cast hmin

/-- The dyadic rounding of a non-increasing series is non-decreasing.  Proved from the
two-sided bound alone, so it needs nothing about how `S` was produced. -/
theorem monotone_of_dyadicRounding {r : ℕ → ℚ} {S : ℕ → ℕ}
    (hround : ∀ i, ((2 : ℝ)⁻¹) ^ S i ≤ (r i : ℝ) ∧ (r i : ℝ) < 2 * ((2 : ℝ)⁻¹) ^ S i)
    (hanti : Antitone r) : Monotone S := by
  intro i j hij
  by_contra hlt
  push Not at hlt
  have hstep : ((2 : ℝ)⁻¹) ^ S i ≤ ((2 : ℝ)⁻¹) ^ (S j + 1) := by
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hrij : (r j : ℝ) ≤ (r i : ℝ) := by exact_mod_cast hanti hij
  have h1 := (hround j).1
  have h2 := (hround i).2
  have hpow : ((2 : ℝ)⁻¹) ^ (S j + 1) = ((2 : ℝ)⁻¹) ^ S j * (2 : ℝ)⁻¹ := by ring
  rw [hpow] at hstep
  linarith

end Kolmogorov
