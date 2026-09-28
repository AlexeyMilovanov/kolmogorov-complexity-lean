import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure.Part01
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.Dimension.AbsolutelyNonRandom
import KolmogorovMathlib.MonotoneComplexity.Dimension.ImageMeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.EffectiveNullDiff
import KolmogorovMathlib.MonotoneComplexity.Dimension.DeficiencySemimeasure
import KolmogorovMathlib.MonotoneComplexity.Dimension.DyadicEndpoint
import KolmogorovMathlib.MonotoneComplexity.Dimension.ArithMeasurePreserving
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.GeneratorComposition
import KolmogorovMathlib.MonotoneComplexity.SemimeasureRealization
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import KolmogorovMathlib.MonotoneComplexity.ExpectationBoundedDeficiency
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

namespace Kolmogorov
open MeasureTheory
open scoped ENNReal

/-! ### The digression of p. 183: Theorem 124

The source proves Theorem 124 inside the proof of Theorem 123(b) ("To prepare
ourselves for this case, let us make a digression and prove that the randomness
deficiency is almost monotone", p. 183), and Theorem 123(b) uses it; so it is
placed here, before Theorem 123(b), rather than after it. -/

/-- There is a lower semicomputable continuous semimeasure `S` which, whenever some prefix `x` of
`y` has deficiency above `k ≥ 1`, satisfies `S y ≥ (2 ^ k / (2 * k ^ 2)) * P(Ω_y)`: the
deficiency-weighted mixture `∑_k P_k / (2 k ^ 2)` of the source.  SUV Theorem 124, §5.9.3,
p. 184. -/
theorem exists_deficiencyWeightedSemimeasure {P : Measure CantorSeq}
    [IsProbabilityMeasure P] (hP : IsComputableMeasure P) :
    ∃ S : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure S ∧
      ∀ (k : ℕ) (x y : BitString) (d : ℝ), 1 ≤ k → x <+: y →
        deficiency P x = (d : EReal) → (k : ℝ) < d →
          ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass P y ≤ S y := by
  refine ⟨defWeightedSemimeasure P, isLSCContinuousSemimeasure_defWeightedSemimeasure hP, ?_⟩
  intro k x y d hk hxy hdx hkd
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  -- `x` has deficiency above `k`, i.e. it is in the `k`-th deficiency set
  have hxD : x ∈ aPrioriDeficiencySet P k := by
    by_contra hcon
    rw [aPrioriDeficiencySet, Set.mem_setOf_eq, not_lt] at hcon
    have hle := deficiency_le_of_apriori_le (P := P) (x := x) (c := k) hcon
    rw [hdx, EReal.coe_le_coe_iff] at hle
    linarith
  -- the root is excluded, since its deficiency is `0`
  have hy : y ≠ [] := by
    intro h0
    subst h0
    have hx0 : x = [] := by
      have hlen := hxy.length_le
      simpa using List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hx0
    have hm : cantorMass P ([] : BitString) = 1 := cantorMass_nil P
    have ha : universalContinuousSemimeasure ([] : BitString) = 1 :=
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.1
    have hnil : deficiency P ([] : BitString) = ((0 : ℝ) : EReal) := by
      rw [deficiency_of_ne_zero (by rw [hm]; norm_num), KA, hm, ha]
      norm_num
    rw [hnil, EReal.coe_eq_coe_iff] at hdx
    rw [← hdx] at hkd
    linarith
  -- above `x` the deficiency set swallows the whole cylinder
  have hsub : cantorCylinder y ⊆ prefixHitSet (aPrioriDeficiencySet P k) := by
    rw [prefixHitSet_eq_iUnion_cantorCylinder]
    intro w hw
    exact Set.mem_biUnion hxD (cantorCylinder_subset_of_prefix hxy hw)
  have hmass : defMeasure P k y = (2 : ℝ≥0∞) ^ k * cantorMass P y := by
    rw [defMeasure_of_ne_nil hy, Set.inter_eq_self_of_subset_left hsub]
    rfl
  have hdom := defMeasure_le_defWeightedSemimeasure (P := P) hk y
  rw [hmass] at hdom
  refine le_trans ?_ hdom
  -- the numeric comparison `1/(2k²) ≤ 2^{-(2·log₂k+1)}`
  set i := Nat.log 2 k with hi
  have hlow : 2 ^ i ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hlowR : (2 : ℝ) ^ i ≤ (k : ℝ) := by exact_mod_cast hlow
  have hnum : ((2 : ℝ)) ^ (2 * i + 1) ≤ 2 * (k : ℝ) ^ 2 := by
    have h1 : ((2 : ℝ)) ^ (2 * i + 1) = 2 * ((2 : ℝ) ^ i) ^ 2 := by
      rw [show 2 * i + 1 = i * 2 + 1 by ring, pow_succ, pow_mul]
      ring
    have h2 : ((2 : ℝ) ^ i) ^ 2 ≤ (k : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
      nlinarith
    rw [h1]
    linarith
  have hsplit : ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2))
      = (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2)) := by
    rw [div_eq_mul_one_div, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hweight : ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2))
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) := by
    rw [← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le]
    have hpow : ((2 : ℝ≥0∞)) ^ (2 * i + 1) = ENNReal.ofReal ((2 : ℝ) ^ (2 * i + 1)) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hpow, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_one.2 ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact hnum
  calc ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass P y
      = (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (1 / (2 * (k : ℝ) ^ 2)) * cantorMass P y := by
        rw [hsplit]
    _ ≤ (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) * cantorMass P y := by gcongr
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (2 * i + 1) * ((2 : ℝ≥0∞) ^ k * cantorMass P y) := by ring

/-- **SUV Theorem 124 (§5.9.3, p. 184).** Let `P` be a computable measure on
`Ω`.  There exists a constant `c` such that for every string `x` and every
string `y` that has `x` as a prefix,

`d_P(y) ≥ d_P(x) - 2 log d_P(x) - c`.

The constant is chosen before `x` and `y`.  The hypothesis
`deficiency P x = (d : EReal)` isolates the case, assumed in the source's proof,
in which `d_P(x)` is finite; the complementary case is
`deficiency_eq_top_of_prefix`.

`1 ≤ d` is the log convention of this file (see the module docstring): the
source's `O(1)` absorbs the range `d < 1`, on which `-2 log d` would be positive
and the printed inequality would be strictly stronger than what the proof gives.
The proof on p. 184 uses the bound only through integers `k ≥ 1` with
`d_P(x) > k`.  Problem 187 uses the same convention. -/
theorem exists_const_deficiency_ge_of_prefix {P : Measure CantorSeq}
    [IsProbabilityMeasure P] (hP : IsComputableMeasure P) :
    ∃ c : ℝ, ∀ (x y : BitString) (d : ℝ), 1 ≤ d → x <+: y →
      deficiency P x = (d : EReal) →
      ((d - 2 * Real.logb 2 d - c : ℝ) : EReal) ≤ deficiency P y := by
  classical
  obtain ⟨S, hScont, hSdom⟩ := exists_deficiencyWeightedSemimeasure hP
  obtain ⟨c₁, hc₁top, hc₁⟩ := universalContinuousSemimeasure_isMaximal S hScont
  obtain ⟨c₀, hc₀top, hc₀⟩ := universalContinuousSemimeasure_isMaximal (cantorMass P)
    ⟨⟨cantorMass_nil P, fun x => le_of_eq (cantorMass_add P x).symm⟩, isLSC_cantorMass hP⟩
  set C₁ : ℝ := (c₁ + 1).toReal with hC₁
  set C₀ : ℝ := (c₀ + 1).toReal with hC₀
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    exact ENNReal.toReal_pos (by simp) (by simp [hc₁top])
  have hC₀pos : 0 < C₀ := by
    rw [hC₀]
    exact ENNReal.toReal_pos (by simp) (by simp [hc₀top])
  have hC₁one : (1 : ℝ) ≤ C₁ := by
    have h1 : ((1 : ℝ≥0∞)).toReal ≤ ((c₁ + 1 : ℝ≥0∞)).toReal :=
      ENNReal.toReal_mono (by simp [hc₁top]) le_add_self
    simpa [hC₁] using h1
  have hC₀one : (1 : ℝ) ≤ C₀ := by
    have h1 : ((1 : ℝ≥0∞)).toReal ≤ ((c₀ + 1 : ℝ≥0∞)).toReal :=
      ENNReal.toReal_mono (by simp [hc₀top]) le_add_self
    simpa [hC₀] using h1
  have hC₁log : 0 ≤ Real.logb 2 C₁ := Real.logb_nonneg (by norm_num) hC₁one
  have hC₀log : 0 ≤ Real.logb 2 C₀ := Real.logb_nonneg (by norm_num) hC₀one
  refine ⟨(2 + Real.logb 2 C₀) + (3 + Real.logb 2 C₁), ?_⟩
  intro x y d hd hxy hdx
  -- the two `toReal` shorthands
  set A : ℝ := (universalContinuousSemimeasure y).toReal with hA
  have hAtop : universalContinuousSemimeasure y ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top y
  have hApos : 0 < A := by
    rw [hA]
    exact ENNReal.toReal_pos (universalContinuousSemimeasure_pos y).ne' hAtop
  by_cases hy0 : cantorMass P y = 0
  · rw [deficiency, if_pos hy0]
    exact le_top
  set Py : ℝ := (cantorMass P y).toReal with hPy
  have hPytop : cantorMass P y ≠ ⊤ := measure_ne_top P _
  have hPypos : 0 < Py := by
    rw [hPy]
    exact ENNReal.toReal_pos hy0 hPytop
  rw [deficiency_of_ne_zero hy0, KA, EReal.coe_le_coe_iff]
  -- the uniform lower bound `d_P(y) ≥ -log C₀`, from `P ≤ C₀ · a`
  have hlow : -Real.logb 2 C₀ ≤ -Real.logb 2 Py - -Real.logb 2 A := by
    have h1 : cantorMass P y ≤ (c₀ + 1) * universalContinuousSemimeasure y :=
      le_trans (hc₀ y) (by gcongr; exact le_self_add)
    have h2 : Py ≤ C₀ * A := by
      rw [hPy, hC₀, hA, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [hc₀top]) hAtop) h1
    have h3 : Real.logb 2 Py ≤ Real.logb 2 C₀ + Real.logb 2 A := by
      calc Real.logb 2 Py ≤ Real.logb 2 (C₀ * A) :=
            (Real.logb_le_logb (by norm_num) hPypos (by positivity)).mpr h2
        _ = Real.logb 2 C₀ + Real.logb 2 A := Real.logb_mul hC₀pos.ne' hApos.ne'
    linarith
  by_cases hbig : (2 : ℝ) ≤ d
  case neg =>
    -- small deficiency: absorbed by the constant
    have hsmall : d < 2 := not_le.1 hbig
    have hlogd : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) hd
    linarith
  case pos =>
    -- the source's argument at `k = ⌊d⌋ - 1`
    set k : ℕ := ⌊d⌋₊ - 1 with hk
    have hfloor_le : (⌊d⌋₊ : ℝ) ≤ d := Nat.floor_le (by linarith)
    have hfloor_lt : d < (⌊d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one d
    have hfloor2 : 2 ≤ ⌊d⌋₊ := by
      have : (2 : ℕ) ≤ ⌊d⌋₊ := Nat.le_floor (by exact_mod_cast hbig)
      exact this
    have hk1 : 1 ≤ k := by omega
    have hkR : (k : ℝ) = (⌊d⌋₊ : ℝ) - 1 := by
      rw [hk]
      have : (1 : ℕ) ≤ ⌊d⌋₊ := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hklt : (k : ℝ) < d := by rw [hkR]; linarith
    have hkge : d - 2 ≤ (k : ℝ) := by rw [hkR]; linarith
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    -- the domination supplied by the leaf, transported to reals
    have hdom := hSdom k x y d hk1 hxy hdx hklt
    have hbound : ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass P y
        ≤ (c₁ + 1) * universalContinuousSemimeasure y :=
      le_trans hdom (le_trans (hc₁ y) (by gcongr; exact le_self_add))
    have hqpos : 0 < (2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2) := by positivity
    have hreal : ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Py ≤ C₁ * A := by
      have hleft : ENNReal.ofReal ((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * cantorMass P y ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPytop
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [hc₁top]) hAtop) hbound
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hqpos.le,
        ← hPy, ← hA, ← hC₁] at this
    have hlogs : Real.logb 2 (((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Py)
        ≤ Real.logb 2 (C₁ * A) :=
      (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr hreal
    have hexpand : Real.logb 2 (((2 : ℝ) ^ k / (2 * (k : ℝ) ^ 2)) * Py)
        = (k : ℝ) - (1 + 2 * Real.logb 2 k) + Real.logb 2 Py := by
      rw [Real.logb_mul (by positivity) hPypos.ne', Real.logb_div (by positivity) (by positivity),
        Real.logb_pow, Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one
          (by norm_num), Real.logb_pow]
      push_cast
      ring
    have hlogk : Real.logb 2 (k : ℝ) ≤ Real.logb 2 d :=
      (Real.logb_le_logb (by norm_num) (by linarith) (by linarith)).mpr (le_of_lt hklt)
    have hsplit : Real.logb 2 (C₁ * A) = Real.logb 2 C₁ + Real.logb 2 A :=
      Real.logb_mul hC₁pos.ne' hApos.ne'
    rw [hexpand, hsplit] at hlogs
    linarith

/-- An infinite set of naturals has elements above any bound. -/
lemma exists_gt_mem_of_infinite {S : Set ℕ} (hS : S.Infinite) (m : ℕ) : ∃ n ∈ S, m < n := by
  by_contra hcon
  push_neg at hcon
  refine hS (Set.Finite.subset (Set.finite_Icc 0 m) fun n hn => ?_)
  simp only [Set.mem_Icc]
  exact ⟨Nat.zero_le _, hcon n hn⟩

/-- A sequence is determined by its prefixes. -/
lemma eq_of_cantorPrefix_eq {σ τ : CantorSeq} (h : ∀ m, cantorPrefix σ m = cantorPrefix τ m) :
    σ = τ := by
  funext i
  have key : ∀ ρ : CantorSeq, (cantorPrefix ρ (i + 1))[i]'(by simp) = ρ i := by
    intro ρ
    simp
  rw [← key σ, ← key τ]
  simp only [h (i + 1)]

/-- Every sequence of strings either takes one value infinitely often, or has a limit branch `ω`
each of whose prefixes is a prefix of infinitely many terms.  SUV §5.9.3, p. 183. -/
theorem exists_repeated_or_limit (W : ℕ → BitString) :
    (∃ w : BitString, {n : ℕ | W n = w}.Infinite) ∨
      ∃ ω : CantorSeq, ∀ m : ℕ, {n : ℕ | cantorPrefix ω m <+: W n}.Infinite := by
  classical
  by_cases hrep : ∃ w : BitString, {n : ℕ | W n = w}.Infinite
  · exact Or.inl hrep
  refine Or.inr ?_
  push_neg at hrep
  -- a string that is a prefix of infinitely many `W n` has such a child
  have hsplit : ∀ p : BitString, {n : ℕ | p <+: W n}.Infinite →
      {n : ℕ | (p ++ [false]) <+: W n}.Infinite ∨ {n : ℕ | (p ++ [true]) <+: W n}.Infinite := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hfin := ((hrep p).union h0).union h1
    refine hp (hfin.subset ?_)
    intro n hn
    obtain ⟨t, ht⟩ := hn
    cases t with
    | nil =>
        exact Or.inl (Or.inl (by simpa using ht.symm))
    | cons b t' =>
        have hb : (p ++ [b]) ++ t' = W n := by
          rw [List.append_assoc]
          simpa using ht
        cases b with
        | false => exact Or.inl (Or.inr ⟨t', hb⟩)
        | true => exact Or.inr ⟨t', hb⟩
  -- the branch
  set nxt : BitString → BitString := fun p =>
    if {n : ℕ | (p ++ [false]) <+: W n}.Infinite then p ++ [false] else p ++ [true] with hnxt
  set g : ℕ → BitString := fun m => Nat.rec ([] : BitString) (fun _ q => nxt q) m with hg
  have hgs : ∀ m, g (m + 1) = nxt (g m) := fun _ => rfl
  have hnxt_pos : ∀ p : BitString, {n : ℕ | (p ++ [false]) <+: W n}.Infinite →
      nxt p = p ++ [false] := by
    intro p h
    simp [hnxt, h]
  have hnxt_neg : ∀ p : BitString, ¬ {n : ℕ | (p ++ [false]) <+: W n}.Infinite →
      nxt p = p ++ [true] := by
    intro p h
    simp [hnxt, h]
  have hglen : ∀ m, (g m).length = m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [hgs]
        by_cases h : {n : ℕ | (g m ++ [false]) <+: W n}.Infinite
        · rw [hnxt_pos _ h]; simp [ih]
        · rw [hnxt_neg _ h]; simp [ih]
  have hgstep : ∀ m, g m <+: g (m + 1) := by
    intro m
    rw [hgs]
    by_cases h : {n : ℕ | (g m ++ [false]) <+: W n}.Infinite
    · rw [hnxt_pos _ h]
      exact ⟨[false], rfl⟩
    · rw [hnxt_neg _ h]
      exact ⟨[true], rfl⟩
  have hgmono : ∀ {m m' : ℕ}, m ≤ m' → g m <+: g m' := by
    intro m m' hmm
    induction m' with
    | zero =>
        have : m = 0 := Nat.le_zero.1 hmm
        rw [this]
    | succ k ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmm) with hlt | heq
        · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (hgstep k)
        · rw [heq]
  have hginf : ∀ m, {n : ℕ | g m <+: W n}.Infinite := by
    intro m
    induction m with
    | zero =>
        have huniv : {n : ℕ | g 0 <+: W n} = Set.univ := by
          ext n
          simp [hg]
        rw [huniv]
        exact Set.infinite_univ
    | succ m ih =>
        rw [hgs]
        by_cases h : {n : ℕ | (g m ++ [false]) <+: W n}.Infinite
        · rw [hnxt_pos _ h]
          exact h
        · rw [hnxt_neg _ h]
          rcases hsplit (g m) ih with h0 | h1
          · exact absurd h0 h
          · exact h1
  refine ⟨fun i => (g (i + 1)).getD i false, fun m => ?_⟩
  have hpref : cantorPrefix (fun i => (g (i + 1)).getD i false) m = g m := by
    refine List.ext_getElem (by simp [hglen]) fun i h1 h2 => ?_
    rw [cantorPrefix_getElem]
    have hi : i < (g (i + 1)).length := by
      have hl := hglen (i + 1)
      omega
    have hle : i + 1 ≤ m := by
      rw [cantorPrefix_length] at h1
      omega
    have hsub := (hgmono hle).getElem hi
    rw [List.getD_eq_getElem _ _ hi, hsub]
  rw [hpref]
  exact hginf m

/-- **SUV Theorem 123(b) (§5.9.3, pp. 181-184).** Any sequence `τ` that is
ML-random with respect to `ν` is the `f`-image of a sequence `ω` that is
ML-random with respect to `μ`. -/
theorem exists_isMartinLofRandom_preimage {μ ν : Measure CantorSeq}
    {f : BitStream → BitStream} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsComputableMeasure μ) (hf : IsComputableStreamMap f)
    (hν : IsImageMeasure μ f ν) {τ : CantorSeq} (hτ : IsMartinLofRandom ν τ) :
    ∃ w : CantorSeq, IsMartinLofRandom μ w ∧
      f (BitStream.infinite w) = BitStream.infinite τ := by
  classical
  have hνcomp : IsComputableMeasure ν := isComputableMeasure_of_isImageMeasure hμ hf hν
  -- the `ν`-deficiencies of the prefixes of `τ` are bounded (randomness criterion)
  obtain ⟨cτ, hcτ⟩ := boundedAPrioriDeficiency_of_isMartinLofRandom hνcomp hτ
  have hmassτ : ∀ n, cantorMass ν (cantorPrefix τ n) ≠ 0 := by
    intro n h0
    have h1 := hcτ n
    rw [h0, mul_zero] at h1
    exact (universalContinuousSemimeasure_pos (cantorPrefix τ n)).ne'
      (le_antisymm h1 (zero_le _))
  have hdefτ : ∀ n, deficiency ν (cantorPrefix τ n) ≤ (((cτ : ℝ)) : EReal) :=
    fun n => deficiency_le_of_apriori_le (hcτ n)
  -- Lemma 2 produces a string of bounded `μ`-deficiency over each prefix of `τ`
  obtain ⟨cL, hcL⟩ := exists_const_forall_exists_deficiency_le hμ hf hν
  choose W hWf hWd using fun n => hcL (cantorPrefix τ n) (hmassτ n)
  set B : ℝ := (cτ : ℝ) + cL with hB
  have hWB : ∀ n, deficiency μ (W n) ≤ ((B : ℝ) : EReal) := by
    intro n
    refine le_trans (hWd n) ?_
    rw [hB, EReal.coe_add]
    exact add_le_add_left (hdefτ n) _
  have hWmass : ∀ n, cantorMass μ (W n) ≠ 0 := by
    intro n h0
    have htop : deficiency μ (W n) = ⊤ := (deficiency_eq_top_iff μ (W n)).2 h0
    have := hWB n
    rw [htop] at this
    simp at this
  -- the source's compactness dichotomy
  rcases exists_repeated_or_limit W with ⟨w, hw⟩ | ⟨ω, hω⟩
  · -- the first case: one string occurs infinitely often, and its image is `τ`
    have hall : ∀ m : ℕ, BitStream.finite (cantorPrefix τ m) ≤ f (BitStream.finite w) := by
      intro m
      obtain ⟨n, hn, hnm⟩ := exists_gt_mem_of_infinite hw m
      have h1 : BitStream.finite (cantorPrefix τ n) ≤ f (BitStream.finite w) := by
        rw [← hn]
        exact hWf n
      refine le_trans ?_ h1
      exact cantorPrefix_mono τ hnm.le
    have hfw : f (BitStream.finite w) = BitStream.infinite τ := by
      cases hfin : f (BitStream.finite w) with
      | finite z =>
          exfalso
          have h1 := hall (z.length + 1)
          rw [hfin] at h1
          have h2 : cantorPrefix τ (z.length + 1) <+: z := h1
          have hlen := h2.length_le
          rw [cantorPrefix_length] at hlen
          omega
      | infinite σ =>
          have hpref : ∀ m, cantorPrefix τ m = cantorPrefix σ m := by
            intro m
            refine List.ext_getElem (by simp) fun i h1 h2 => ?_
            have h3 := hall m
            rw [hfin] at h3
            have h4 : IsCantorPrefix (cantorPrefix τ m) σ := h3
            rw [cantorPrefix_length] at h1
            have h5 := h4 i (by simpa using h1)
            simpa using h5.symm
          rw [eq_of_cantorPrefix_eq (fun m => (hpref m).symm)]
    obtain ⟨n₀, hn₀⟩ := hw.nonempty
    have hwmass : cantorMass μ w ≠ 0 := by
      rw [← hn₀]
      exact hWmass n₀
    obtain ⟨x, hxw, hxr⟩ := exists_isMartinLofRandom_mem_cantorCylinder hμ hwmass
    refine ⟨x, hxr, ?_⟩
    have hmono : f (BitStream.finite w) ≤ f (BitStream.infinite x) :=
      hf.1.1 (by exact hxw)
    rw [hfw] at hmono
    cases hfx : f (BitStream.infinite x) with
    | finite z =>
        exfalso
        rw [hfx] at hmono
        exact hmono
    | infinite σ =>
        rw [hfx] at hmono
        have hστ : τ = σ := hmono
        rw [hστ]
  · -- the second case: the strings converge to `ω`
    obtain ⟨c124, hc124⟩ := exists_const_deficiency_ge_of_prefix (P := μ) hμ
    have hprefmass : ∀ m, cantorMass μ (cantorPrefix ω m) ≠ 0 := by
      intro m h0
      obtain ⟨n, hn, -⟩ := exists_gt_mem_of_infinite (hω m) 0
      have hsub : cantorMass μ (W n) ≤ cantorMass μ (cantorPrefix ω m) := by
        simp only [cantorMass]
        exact measure_mono (cantorCylinder_subset_of_prefix hn)
      rw [h0] at hsub
      exact hWmass n (le_antisymm hsub (zero_le _))
    have hdefreal : ∀ m, ∃ d : ℝ, deficiency μ (cantorPrefix ω m) = (d : EReal) :=
      fun m => ⟨_, deficiency_of_ne_zero (hprefmass m)⟩
    choose D hD using hdefreal
    set K : ℝ := max 64 (2 * (B + c124)) with hK
    have hDbound : ∀ m, D m ≤ K := by
      intro m
      by_cases h1 : (1 : ℝ) ≤ D m
      · obtain ⟨n, hn, -⟩ := exists_gt_mem_of_infinite (hω m) 0
        have h124 := hc124 (cantorPrefix ω m) (W n) (D m) h1 hn (hD m)
        have hle : ((D m - 2 * Real.logb 2 (D m) - c124 : ℝ) : EReal) ≤ ((B : ℝ) : EReal) :=
          le_trans h124 (hWB n)
        rw [EReal.coe_le_coe_iff] at hle
        exact le_of_sub_two_logb_le h1 (by linarith)
      · push_neg at h1
        have h2 : (1 : ℝ) ≤ K := le_trans (by norm_num) (le_max_left _ _)
        linarith
    have hωrand : IsMartinLofRandom μ ω := by
      refine isMartinLofRandom_of_boundedAPrioriDeficiency hμ ⟨⌈K⌉₊, fun m => ?_⟩
      refine apriori_le_of_deficiency_le (hprefmass m) ?_
      rw [hD m, EReal.coe_le_coe_iff]
      exact le_trans (hDbound m) (Nat.le_ceil K)
    obtain ⟨σ, hσ⟩ := exists_infinite_comp_of_isMartinLofRandom hμ hf hν hωrand
    refine ⟨ω, hωrand, ?_⟩
    rw [hσ]
    have hpref : ∀ m : ℕ, cantorPrefix σ m = cantorPrefix τ m := by
      intro m
      have h1 : BitStream.finite (cantorPrefix σ m) ≤ f (BitStream.infinite ω) := by
        rw [hσ]
        exact mem_cantorCylinder_cantorPrefix σ m
      obtain ⟨N, hN⟩ :=
        (continuousStreamMap_finite_le_infinite_iff f hf.1 ω (cantorPrefix σ m)).1 h1
      obtain ⟨n, hn, hnm⟩ := exists_gt_mem_of_infinite (hω N) m
      have h2 : BitStream.finite (cantorPrefix σ m) ≤ f (BitStream.finite (W n)) :=
        le_trans hN (hf.1.1 (by exact hn))
      have h3 : BitStream.finite (cantorPrefix τ n) ≤ f (BitStream.finite (W n)) := hWf n
      have hcomp : cantorPrefix σ m <+: cantorPrefix τ n := by
        refine prefix_of_finite_le_finite_le h2 h3 ?_
        simp only [cantorPrefix_length]
        omega
      have hcomp' : cantorPrefix τ m <+: cantorPrefix τ n := cantorPrefix_mono τ hnm.le
      have hle : (cantorPrefix σ m).length ≤ (cantorPrefix τ m).length := by simp
      have := List.prefix_of_prefix_length_le hcomp hcomp' hle
      exact this.eq_of_length (by simp)
    rw [eq_of_cantorPrefix_eq hpref]

/- ## Expectation-bounded deficiency of infinite sequences (§3.5, for §5.9.3)

`ennrealLogbTwo`, `IsMaximalExpectationBoundedTest` and
`exists_isMaximalExpectationBoundedTest` moved unchanged (same names, same statements) to
`KolmogorovMathlib.MonotoneComplexity.ExpectationBoundedDeficiency`, which is imported above;
they belong beside the expectation-bounded test API.  Problem 185 in
`Dimension/Exercises.lean` uses them from there. -/


/-! ## §5.9.1 concluded: Theorem 121

The three theorems of §5.9.1 sit here, at the end of the module, because their
proof runs through Theorem 123(a) (`image_isMartinLofRandom_of_isMartinLofRandom`
of §5.9.3): the transfer of randomness along the two interval maps is the
image-randomness theorem applied to the two measure-preservation identities of
`Dimension/ArithMeasurePreserving.lean`.  The statements are unchanged. -/


/-- **Leaf (SUV Theorem 121, §5.9.1, p. 177): obligation (c), the transfer of
randomness and the mutual inversion.**  The two interval maps of the source's
proof are `invArithMap μ` (the direction `μ → uniform`, `ω ↦ r(ω)`) and
`arithMap μ` (the direction `uniform → μ`); both are computable stream maps
(`isComputableStreamMap_invArithMap`, `isComputableStreamMap_arithMap`) and both
are *total* on the relevant random sequences
(`exists_infinite_invArithMap_of_isMartinLofRandom`,
`exists_infinite_arithMap_of_isMartinLofRandom`).  What is left of Theorem 121's
uniform case is the source's sentence

> "The computability of the measure guarantees that effectively null sets with
> respect to `μ₁` correspond to the effectively null sets with respect to the
> uniform measure, therefore we get a bijection between the sets of ML-random
> sequences with respect to corresponding measures." (p. 177)

* `IsImageMeasure μ (invArithMap μ) uniformMeasure`, and
* `IsImageMeasure uniformMeasure (arithMap μ) μ`,

which unwind, through `streamLowerGraph_invArithMap_infinite` and
`streamLowerGraph_arithMap_infinite`, into the two measure-preservation
identities of `Dimension/ArithMeasurePreserving.lean`:

* `μ (prefixHitSet {x | invArithGraph μ x p}) = cantorMass uniformMeasure p`
  (`measure_prefixHitSet_invArithGraph`), and
* `uniformMeasure (prefixHitSet {p | arithmeticCodingLowerGraph μ p x})
  = cantorMass μ x` (`uniformMeasure_prefixHitSet_arithmeticCodingLowerGraph`),

i.e. that the interval construction preserves measure in both directions.  Each
of the two is one instance of `measure_prefixHitSet_treeWindowSet`: the mass of
the sequences having a prefix whose interval sits strictly inside a window
`(α, β) ⊆ [0,1]` is exactly `β - α`, whenever the two endpoint fibres are null.
On the dyadic side the window is `(k/2^n, (k+1)/2^n)`; on the uniform side it is
`(L_μ(x), L_μ(x) + μ(Ω_x))`, whose endpoints are *not* dyadic -- which is why
the window lemma is stated for arbitrary real endpoints.  The endpoint fibres
are null by the endpoint tests of `Dimension/DyadicEndpoint.lean`, i.e. by
SUV p. 177's "the endpoints of the segments ... are not random".

The *mutual inversion* is no longer part of this leaf: it is proved, as
`arithMap_invArithMap_of_isMartinLofRandom` and
`invArithMap_arithMap_of_isMartinLofRandom` in
`Dimension/DyadicEndpoint.lean`, by the lower-graph computation the source's
argument suggests -- each map's output denotes the same real as its input
(`treeReal_invArithMap_eq_measureReal`, `measureReal_arithMap_eq_treeReal`), and
the strings the other map then prints are exactly the prefixes of the original
argument, because that real lies in the *interior* of the corresponding cell
(`measureReal_ne_treeEnd_of_isMartinLofRandom`, which rules out both endpoints,
i.e. the source's `x000⋯` and `x111⋯`) and cells of equal length are separated
by `prefix_or_prefix_of_mem_treeIco`. -/
theorem isMartinLofRandom_transfer_arithMap {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : IsAtomlessMeasure μ) :
    (∀ w v : CantorSeq, IsMartinLofRandom μ w →
        invArithMap μ (BitStream.infinite w) = BitStream.infinite v →
        IsMartinLofRandom uniformMeasure v) ∧
      (∀ v u : CantorSeq, IsMartinLofRandom uniformMeasure v →
        arithMap μ (BitStream.infinite v) = BitStream.infinite u →
        IsMartinLofRandom μ u) := by
  have him1 : IsImageMeasure μ (invArithMap μ) uniformMeasure := by
    intro p
    have hset : {w : CantorSeq | BitStream.finite p ≤ invArithMap μ (BitStream.infinite w)}
        = prefixHitSet {x : BitString | invArithGraph μ x p} :=
      Set.ext fun w => streamLowerGraph_invArithMap_infinite μ w p
    rw [hset]
    exact (measure_prefixHitSet_invArithGraph μ hμ haμ p).symm
  have him2 : IsImageMeasure uniformMeasure (arithMap μ) μ := by
    intro x
    have hset : {v : CantorSeq | BitStream.finite x ≤ arithMap μ (BitStream.infinite v)}
        = prefixHitSet {p : BitString | arithmeticCodingLowerGraph μ p x} :=
      Set.ext fun v => streamLowerGraph_arithMap_infinite μ v x
    rw [hset]
    exact (uniformMeasure_prefixHitSet_arithmeticCodingLowerGraph μ hμ x).symm
  refine ⟨fun w v hw hwv => ?_, fun v u hv hvu => ?_⟩
  · obtain ⟨v', hv', hv'r⟩ := image_isMartinLofRandom_of_isMartinLofRandom hμ
      (isComputableStreamMap_invArithMap μ hμ) him1 hw
    rw [hwv] at hv'
    obtain rfl : v = v' := by simpa using hv'
    exact hv'r
  · obtain ⟨u', hu', hu'r⟩ := image_isMartinLofRandom_of_isMartinLofRandom
      isComputableMeasure_uniform (isComputableStreamMap_arithMap μ hμ) him2 hv
    rw [hvu] at hu'
    obtain rfl : u = u' := by simpa using hu'
    exact hu'r

/-- **Leaf (SUV Theorem 121, §5.9.1, pp. 176-177): the uniform case.**  For a
computable atomless measure there is a computable bijection, in both directions
the restriction of a computable stream map, between its ML-random sequences and
the uniformly ML-random ones.

This is the case the source treats; the general statement follows from it by
composing the two bijections through the uniform measure, which is what
`exists_computableStreamMap_bijection_isMartinLofRandom` does below:

> "Following [225], consider first a special case when one of the measures (say,
> `μ₂`) is the uniform measure on `[0,1]`. […]  It remains to do the same for
> `μ₂` and then take the composition of these two bijections (using `[0,1]` as
> an intermediate step)." (pp. 176-177) -/
theorem exists_computableStreamMap_bijection_uniform {μ : Measure CantorSeq}
    [IsProbabilityMeasure μ] (hμ : IsComputableMeasure μ) (haμ : IsAtomlessMeasure μ) :
    ∃ f g : BitStream → BitStream, IsComputableStreamMap f ∧ IsComputableStreamMap g ∧
      (∀ w : CantorSeq, IsMartinLofRandom μ w → ∃ v : CantorSeq,
        f (BitStream.infinite w) = BitStream.infinite v ∧
          IsMartinLofRandom uniformMeasure v) ∧
      (∀ v : CantorSeq, IsMartinLofRandom uniformMeasure v → ∃ w : CantorSeq,
        g (BitStream.infinite v) = BitStream.infinite w ∧ IsMartinLofRandom μ w) ∧
      (∀ w : CantorSeq, IsMartinLofRandom μ w →
        g (f (BitStream.infinite w)) = BitStream.infinite w) ∧
      (∀ v : CantorSeq, IsMartinLofRandom uniformMeasure v →
        f (g (BitStream.infinite v)) = BitStream.infinite v) := by
  obtain ⟨h1, h2⟩ := isMartinLofRandom_transfer_arithMap hμ haμ
  refine ⟨invArithMap μ, arithMap μ, isComputableStreamMap_invArithMap μ hμ,
    isComputableStreamMap_arithMap μ hμ, ?_, ?_,
    fun w hw => arithMap_invArithMap_of_isMartinLofRandom μ hμ haμ hw,
    fun v hv => invArithMap_arithMap_of_isMartinLofRandom μ hμ haμ hv⟩
  · intro w hw
    obtain ⟨v, hv⟩ := exists_infinite_invArithMap_of_isMartinLofRandom μ hμ haμ hw
    exact ⟨v, hv, h1 w v hw hv⟩
  · intro v hv
    obtain ⟨u, hu⟩ := exists_infinite_arithMap_of_isMartinLofRandom μ hμ hv
    exact ⟨u, hu, h2 v u hv hu⟩

/-- **SUV Theorem 121 (§5.9.1, p. 176).** For two computable atomless measures
`μ₁`, `μ₂` there is a bijection between the sets of ML-random sequences with
respect to `μ₁` and `μ₂` that in both directions is a restriction of a
computable mapping of type `Σ → Σ`.

The two computable stream maps `f`, `g` send random sequences to (infinite)
random sequences and are mutually inverse on the two sets of random sequences,
which is exactly the source's bijection. -/
theorem exists_computableStreamMap_bijection_isMartinLofRandom
    {μ₁ μ₂ : Measure CantorSeq} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsComputableMeasure μ₁) (h₂ : IsComputableMeasure μ₂)
    (ha₁ : IsAtomlessMeasure μ₁) (ha₂ : IsAtomlessMeasure μ₂) :
    ∃ f g : BitStream → BitStream, IsComputableStreamMap f ∧ IsComputableStreamMap g ∧
      (∀ w : CantorSeq, IsMartinLofRandom μ₁ w → ∃ v : CantorSeq,
        f (BitStream.infinite w) = BitStream.infinite v ∧ IsMartinLofRandom μ₂ v) ∧
      (∀ v : CantorSeq, IsMartinLofRandom μ₂ v → ∃ w : CantorSeq,
        g (BitStream.infinite v) = BitStream.infinite w ∧ IsMartinLofRandom μ₁ w) ∧
      (∀ w : CantorSeq, IsMartinLofRandom μ₁ w →
        g (f (BitStream.infinite w)) = BitStream.infinite w) ∧
      (∀ v : CantorSeq, IsMartinLofRandom μ₂ v →
        f (g (BitStream.infinite v)) = BitStream.infinite v) := by
  obtain ⟨f₁, g₁, hf₁, hg₁, hf₁r, hg₁r, hgf₁, hfg₁⟩ :=
    exists_computableStreamMap_bijection_uniform h₁ ha₁
  obtain ⟨f₂, g₂, hf₂, hg₂, hf₂r, hg₂r, hgf₂, hfg₂⟩ :=
    exists_computableStreamMap_bijection_uniform h₂ ha₂
  refine ⟨fun s => g₂ (f₁ s), fun s => g₁ (f₂ s), hg₂.comp hf₁, hg₁.comp hf₂, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hvr⟩ := hf₁r w hw
    obtain ⟨x, hx, hxr⟩ := hg₂r v hvr
    refine ⟨x, ?_, hxr⟩
    change g₂ (f₁ (BitStream.infinite w)) = BitStream.infinite x
    rw [hv, hx]
  · intro v hv
    obtain ⟨t, ht, htr⟩ := hf₂r v hv
    obtain ⟨x, hx, hxr⟩ := hg₁r t htr
    refine ⟨x, ?_, hxr⟩
    change g₁ (f₂ (BitStream.infinite v)) = BitStream.infinite x
    rw [ht, hx]
  · intro w hw
    obtain ⟨v, hv, hvr⟩ := hf₁r w hw
    obtain ⟨x, hx, hxr⟩ := hg₂r v hvr
    have hback : f₂ (BitStream.infinite x) = BitStream.infinite v := by
      rw [← hx]
      exact hfg₂ v hvr
    calc g₁ (f₂ (g₂ (f₁ (BitStream.infinite w)))) = g₁ (f₂ (BitStream.infinite x)) := by
          rw [hv, hx]
      _ = g₁ (f₁ (BitStream.infinite w)) := by rw [hback, hv]
      _ = BitStream.infinite w := hgf₁ w hw
  · intro v hv
    obtain ⟨t, ht, htr⟩ := hf₂r v hv
    obtain ⟨x, hx, hxr⟩ := hg₁r t htr
    have hback : f₁ (BitStream.infinite x) = BitStream.infinite t := by
      rw [← hx]
      exact hfg₁ t htr
    calc g₂ (f₁ (g₁ (f₂ (BitStream.infinite v)))) = g₂ (f₁ (BitStream.infinite x)) := by
          rw [ht, hx]
      _ = g₂ (f₂ (BitStream.infinite v)) := by rw [hback, ht]
      _ = BitStream.infinite v := hgf₂ v hv

end Kolmogorov


